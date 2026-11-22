-- Prove2me | solution 1 for rademacher_lower_bound_on_shattered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:06.429244+00:00
-- url     : https://prove2.me/submissions/e80ddfbf-a20f-4c64-b835-366c06e4f635

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_rademacherCorrelation_abs_le_one
public import Theorems.Thm_empiricalRademacherComplexity_le_one
public import Theorems.Thm_uniformMeasure_isProbability

section
@[expose] public section
universe u v
private theorem flipAt_involutive {m : ℕ} (i : Fin m) : Function.Involutive (flipAt i) := by
  intro σ; ext k; unfold flipAt
  simp_all
private theorem flipAt_boolToSign {m : ℕ} (i : Fin m) (σ : SignVector m) :
    boolToSign (flipAt i σ i) = -boolToSign (σ i) := by
  unfold flipAt; simp only [Function.update_self]
  unfold boolToSign; cases σ i <;> simp
private theorem flipAt_other {m : ℕ} (i : Fin m) (σ : SignVector m) (k : Fin m) (hk : k ≠ i) :
    flipAt i σ k = σ k := by
  unfold flipAt; simp [hk]
private theorem sum_boolToSign_cancel {m : ℕ} (i : Fin m) (f : SignVector m → ℝ)
    (hf : ∀ σ σ', (∀ k, k ≠ i → σ k = σ' k) → f σ = f σ') :
    ∑ σ : SignVector m, boolToSign (σ i) * f σ = 0 := by
  -- Use the involution flipAt i to show S = -S, hence S = 0.
  have hinv := flipAt_involutive i
  set g : SignVector m → ℝ := fun σ => boolToSign (σ i) * f σ
  -- Reindex: Σ g(σ) = Σ g(flipAt i σ) since flipAt i is a bijection.
  have h_eq : ∑ σ : SignVector m, g σ =
      ∑ σ : SignVector m, g (flipAt i σ) := by
    let e : SignVector m ≃ SignVector m := Equiv.ofBijective (flipAt i) hinv.bijective
    rw [show ∑ σ, g (flipAt i σ) = ∑ σ, g (e σ) from rfl]
    exact (Equiv.sum_comp e g).symm
  -- g(flipAt i σ) = -g(σ) since flipAt negates boolToSign at i but preserves f.
  have h_neg : ∀ σ, g (flipAt i σ) = -g σ := by
    intro σ
    change boolToSign (flipAt i σ i) * f (flipAt i σ) =
      -(boolToSign (σ i) * f σ)
    rw [flipAt_boolToSign, hf (flipAt i σ) σ (fun k hk => flipAt_other i σ k hk)]
    ring
  -- So S = Σ g(σ) = Σ -g(σ) = -S.
  have h_neg_sum : ∑ σ : SignVector m, g σ = -(∑ σ : SignVector m, g σ) := by
    conv_lhs => rw [h_eq]
    simp_rw [h_neg]
    simp [Finset.sum_neg_distrib]
  linarith
private theorem empRad_nonneg {X : Type u} (C : ConceptClass X Bool) {m : ℕ}
    (hm : m ≠ 0) (xs : Fin m → X) :
    0 ≤ EmpiricalRademacherComplexity X C xs := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg hm]
  apply mul_nonneg
  · apply div_nonneg one_pos.le; exact Nat.cast_nonneg _
  · by_cases hC : C.Nonempty
    · obtain ⟨h₀, hh₀⟩ := hC
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        intro σ; refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm_pos h' σ xs)
      have h_ge : ∀ σ : SignVector m,
          rademacherCorrelation h₀ σ xs ≤
            sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
        fun σ => le_csSup_of_le (hbdd σ) ⟨h₀, hh₀, rfl⟩ le_rfl
      have h_sum_corr : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg hm]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      calc (0 : ℝ) = ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs := h_sum_corr.symm
        _ ≤ ∑ σ : SignVector m,
              sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
            Finset.sum_le_sum (fun σ _ => h_ge σ)
    · rw [Set.not_nonempty_iff_eq_empty] at hC
      simp_all
private theorem corr_eq_one_of_agree {X : Type u} {m : ℕ} (hm : 0 < m)
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X)
    (hagree : ∀ i : Fin m, h (xs i) = σ i) :
    rademacherCorrelation h σ xs = 1 := by
  unfold rademacherCorrelation
  rw [dif_neg (by omega)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- Each term boolToSign(σ i) * boolToSign(h(xs i)) = boolToSign(σ i)² = 1
  have h_terms : ∀ i : Fin m,
      boolToSign (σ i) * boolToSign (h (xs i)) = 1 := by
    intro i; rw [hagree i]; unfold boolToSign; cases σ i <;> simp
  simp_rw [h_terms]
  simp [Finset.sum_const]
  field_simp
private theorem shatters_subset {X : Type u} (C : ConceptClass X Bool)
    (T S : Finset X) (hTS : S ⊆ T) (hT : Shatters X C T) :
    Shatters X C S := by
  classical
  intro f
  -- Extend f to a labeling of T: f on S, true elsewhere
  let g : ↥T → Bool := fun ⟨x, _⟩ =>
    if hxS : x ∈ S then f ⟨x, hxS⟩ else true
  obtain ⟨c, hcC, hcT⟩ := hT g
  refine ⟨c, hcC, fun ⟨x, hxS⟩ => ?_⟩
  have hxT : x ∈ T := hTS hxS
  have h := hcT ⟨x, hxT⟩
  change c x = f ⟨x, hxS⟩
  rw [h]; show g ⟨x, hxT⟩ = f ⟨x, hxS⟩
  simp only [g, dif_pos hxS]
private theorem empRad_eq_one_of_all_labelings {X : Type u}
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (h_realize : ∀ σ : SignVector m, ∃ h ∈ C, ∀ i : Fin m, h (xs i) = σ i) :
    EmpiricalRademacherComplexity X C xs = 1 := by
  -- For each σ, sSup = 1.
  have h_ssup_eq_one : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = 1 := by
    intro σ
    apply le_antisymm
    · -- sSup ≤ 1
      apply csSup_le
      · obtain ⟨c, hcC, _⟩ := h_realize σ
        exact ⟨rademacherCorrelation c σ xs, c, hcC, rfl⟩
      · rintro r ⟨h, _, rfl⟩
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h σ xs)
    · -- sSup ≥ 1: use h with corr = 1
      obtain ⟨c, hcC, hc_agree⟩ := h_realize σ
      have hcorr : rademacherCorrelation c σ xs = 1 :=
        corr_eq_one_of_agree hm c σ xs hc_agree
      have hbdd : BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h' σ xs)
      exact le_csSup_of_le hbdd ⟨c, hcC, rfl⟩ (by rw [hcorr])
  -- EmpRad = (1/N) * Σ_σ 1 = 1
  unfold EmpiricalRademacherComplexity
  rw [dif_neg (by omega)]
  simp_all
private theorem empRad_eq_one_of_injective_in_shattered {X : Type u}
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m)
    (T : Finset X) (hT : Shatters X C T)
    (xs : Fin m → X) (h_inj : Function.Injective xs)
    (h_range : ∀ i : Fin m, xs i ∈ T) :
    EmpiricalRademacherComplexity X C xs = 1 := by
  classical
  apply empRad_eq_one_of_all_labelings C hm xs
  intro σ
  set S := Finset.univ.image xs with hS_def
  have hS_sub : S ⊆ T := by
    intro x hx
    simp only [hS_def, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h_range i
  have hS_shat : Shatters X C S := shatters_subset C T S hS_sub hT
  let f : ↥S → Bool := fun ⟨x, hx⟩ => σ (Finset.mem_image.mp hx).choose
  obtain ⟨c, hcC, hc_agree⟩ := hS_shat f
  refine ⟨c, hcC, fun i => ?_⟩
  have hxs_in_S : xs i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have h_agree_i := hc_agree ⟨xs i, hxs_in_S⟩
  change c (xs i) = σ i
  rw [h_agree_i]
  change σ (Finset.mem_image.mp hxs_in_S).choose = σ i
  congr 1
  apply h_inj
  exact (Finset.mem_image.mp hxs_in_S).choose_spec.2
private theorem uniform_injective_tuple_measure_half
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (hne : Nonempty α) (m : ℕ) (hlarge : 4 * m ^ 2 + 1 ≤ Fintype.card α) :
    let D_sub := uniformMeasure α hne
    let μ_sub := MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)
    (1 : ℝ) / 2 ≤ (μ_sub {ys : Fin m → α | Function.Injective ys}).toReal := by
  classical
  intro D_sub μ_sub
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hne
  have hD_sub_prob : MeasureTheory.IsProbabilityMeasure D_sub :=
    uniformMeasure_isProbability α hne hpos
  have : MeasureTheory.IsProbabilityMeasure μ_sub :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  set B := {ys : Fin m → α | Function.Injective ys}
  have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
  set n := Fintype.card α with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact hpos
  have hn_ne : (n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_nt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hDsub_sing : ∀ t : α, D_sub {t} = 1 / (n : ENNReal) := by
    intro t
    simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    simp_all
  have : MeasureTheory.IsFiniteMeasure D_sub := by
    constructor; rw [hD_sub_prob.measure_univ]; exact ENNReal.one_lt_top
  have : MeasureTheory.SigmaFinite D_sub :=
    @MeasureTheory.IsFiniteMeasure.toSigmaFinite α _ D_sub inferInstance
  set pairs := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2) with pairs_def
  have hBc_sub : Bᶜ ⊆ ⋃ p ∈ pairs, {ys : Fin m → α | ys p.1 = ys p.2} := by
    intro ys hys
    rw [Set.mem_compl_iff] at hys
    change ¬ Function.Injective ys at hys
    rw [Function.Injective] at hys
    push Not at hys
    obtain ⟨i, j, hij_eq, hij_ne⟩ := hys
    rw [Set.mem_iUnion]
    rcases lt_or_gt_of_ne hij_ne with h | h
    · exact ⟨(i, j), Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hij_eq⟩⟩
    · exact ⟨(j, i), Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hij_eq.symm⟩⟩
  have hD_univ : D_sub Set.univ = 1 := hD_sub_prob.measure_univ
  have hcoll_bound : ∀ p ∈ pairs,
      μ_sub {ys : Fin m → α | ys p.1 = ys p.2} ≤ 1 / (n : ENNReal) := by
    intro ⟨i, j⟩ hp
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hp).2
    set Cij := {ys : Fin m → α | ys i = ys j}
    have hCij_eq : Cij = ⋃ t : α, {ys : Fin m → α | ys i = t ∧ ys j = t} := by
      ext ys; simp only [Cij, Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun h => ⟨ys i, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2.symm⟩
    have hcyl : ∀ t : α, {ys : Fin m → α | ys i = t ∧ ys j = t} =
        Set.pi Set.univ (fun k => if k = i then {t} else if k = j then {t} else Set.univ) := by
      intro t; ext ys
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro ⟨h1, h2⟩ k
        split_ifs with hki hkj
        · exact hki ▸ h1
        · exact hkj ▸ h2
        · trivial
      · intro h
        constructor
        · simpa using h i
        · simpa [Ne.symm hij] using h j
    have hfiber_bound : ∀ t : α,
        μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} ≤ (1 / (n : ENNReal)) ^ 2 := by
      intro t
      rw [hcyl t]
      change (MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)) _ ≤ _
      rw [MeasureTheory.Measure.pi_pi]
      have hfact_le : ∀ k : Fin m,
          D_sub (if k = i then {t} else if k = j then {t} else Set.univ) ≤
          (if k = i then 1 / (n : ENNReal) else if k = j then 1 / (n : ENNReal) else 1) := by
        intro k; split_ifs <;> [rw [hDsub_sing]; rw [hDsub_sing]; rw [hD_univ]]
      have hfact_eq : ∀ k : Fin m,
          (if k = i then 1 / (n : ENNReal) else if k = j then 1 / (n : ENNReal) else 1) =
          (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) := by
        intro k; split_ifs with h1 h2 h3 <;> simp_all
      calc ∏ k : Fin m, D_sub (if k = i then {t} else if k = j then {t} else Set.univ)
          ≤ ∏ k : Fin m,
              (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) := by
            apply Finset.prod_le_prod (fun _ _ => bot_le)
            intro k _; exact (hfact_eq k) ▸ (hfact_le k)
        _ = (1 / (n : ENNReal)) ^ 2 := by
            have hprod_ij : ∏ k : Fin m,
                (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) =
                1 / (n : ENNReal) * (1 / (n : ENNReal)) := by
              have hi_mem : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
              rw [← Finset.mul_prod_erase _ _ hi_mem]
              have hj_in : j ∈ (Finset.univ : Finset (Fin m)).erase i :=
                Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
              rw [← Finset.mul_prod_erase _ _ hj_in]
              have hrest_eq : ∏ k ∈ ((Finset.univ : Finset (Fin m)).erase i).erase j,
                  (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) = 1 := by
                apply Finset.prod_eq_one; simp_all
              simp_all
            rw [hprod_ij, sq]
    calc μ_sub Cij
        ≤ ∑ t : α, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} := by
          rw [hCij_eq]
          calc μ_sub (⋃ t, {ys : Fin m → α | ys i = t ∧ ys j = t})
              ≤ ∑' t, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} :=
                MeasureTheory.measure_iUnion_le _
            _ = ∑ t, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} := tsum_fintype _
      _ ≤ ∑ _t : α, (1 / (n : ENNReal)) ^ 2 :=
          Finset.sum_le_sum (fun t _ => hfiber_bound t)
      _ = (n : ENNReal) * (1 / (n : ENNReal)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, hn_def, nsmul_eq_mul]
      _ = 1 / (n : ENNReal) := by
          rw [sq, ← mul_assoc]
          have h1n : (↑n : ENNReal) * (1 / ↑n) = 1 := by
            rw [one_div, ENNReal.mul_inv_cancel hn_ne hn_nt]
          rw [h1n, one_mul]
  have hBc_le : μ_sub Bᶜ ≤ pairs.card * (1 / (n : ENNReal)) :=
    calc μ_sub Bᶜ
        ≤ μ_sub (⋃ p ∈ pairs, {ys : Fin m → α | ys p.1 = ys p.2}) :=
          MeasureTheory.measure_mono hBc_sub
      _ ≤ ∑ p ∈ pairs, μ_sub {ys : Fin m → α | ys p.1 = ys p.2} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ pairs, (1 / (n : ENNReal)) :=
          Finset.sum_le_sum hcoll_bound
      _ = pairs.card * (1 / (n : ENNReal)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpairs_card : pairs.card ≤ m * m :=
    calc pairs.card
        ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_filter_le _ _
      _ = Fintype.card (Fin m × Fin m) := Finset.card_univ
      _ = Fintype.card (Fin m) * Fintype.card (Fin m) := Fintype.card_prod _ _
      _ = m * m := by simp [Fintype.card_fin]
  have h2mm_le_n : 2 * (m * m) ≤ n := by rw [hn_def]; nlinarith [hlarge]
  have hBc_half : μ_sub Bᶜ ≤ 1 / 2 := by
    have hmm_le : (m * m : ℕ) * (1 / (n : ENNReal)) ≤ 1 / 2 := by
      have h_key : (↑(m * m) : ENNReal) ≤ (↑n : ENNReal) / 2 := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
        calc (↑(m * m) : ENNReal) * 2 = ↑(m * m * 2 : ℕ) := by push_cast; ring
          _ ≤ ↑n := Nat.cast_le.mpr (by nlinarith [h2mm_le_n])
      calc (↑(m * m) : ENNReal) * (1 / ↑n)
          ≤ (↑n / 2) * (1 / ↑n) :=
            mul_le_mul_of_nonneg_right h_key (by positivity)
        _ = 1 / 2 := by
            rw [one_div (↑n : ENNReal)]
            rw [div_eq_mul_inv, mul_assoc, mul_comm (2 : ENNReal)⁻¹ (↑n)⁻¹,
                ← mul_assoc, ENNReal.mul_inv_cancel hn_ne hn_nt, one_mul, inv_eq_one_div]
    exact (hBc_le.trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hpairs_card) (by positivity))).trans hmm_le
  have hB_le_one : μ_sub B ≤ 1 :=
    (MeasureTheory.measure_mono (Set.subset_univ B)).trans (le_of_eq MeasureTheory.measure_univ)
  have hcompl := MeasureTheory.prob_compl_eq_one_sub hB_meas (μ := μ_sub)
  have hB_ge : 1 / 2 ≤ μ_sub B := by
    rw [hcompl] at hBc_half
    have h1 : 1 - (1 : ENNReal) / 2 ≤ 1 - (1 - μ_sub B) :=
      tsub_le_tsub_left hBc_half 1
    simp only [show (1 : ENNReal) - 1 / 2 = 1 / 2 from by norm_num] at h1
    rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hB_le_one] at h1
  have hB_ne_top : μ_sub B ≠ ⊤ := MeasureTheory.measure_ne_top μ_sub B
  have h_half_real : ((1 : ENNReal) / 2).toReal = (1 : ℝ) / 2 := by norm_num
  calc (1 : ℝ) / 2 = ((1 : ENNReal) / 2).toReal := h_half_real.symm
    _ ≤ (μ_sub B).toReal := ENNReal.toReal_mono hB_ne_top hB_ge
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (T : Finset X) (hT : Shatters X C T)
    (m : ℕ) (hm : 0 < m) (hT_large : 4 * m ^ 2 + 1 ≤ T.card) :
    ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      (1 : ℝ) / 2 ≤ RademacherComplexity X C D m := by
  classical
  have hT_ne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hT_large
  have hT_card_pos : 0 < T.card := Finset.Nonempty.card_pos hT_ne
  -- Construct D = uniform on T via pushforward from ↥T.
  have : Fintype ↥T := T.fintypeCoeSort
  let msT : MeasurableSpace ↥T := ⊤
  have : @MeasurableSingletonClass ↥T ⊤ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hT_ne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := by rw [Fintype.card_coe]; exact hT_card_pos
  let D_sub := @uniformMeasure ↥T ⊤ _ hTne_type
  have hD_sub_prob : @MeasureTheory.IsProbabilityMeasure ↥T ⊤ D_sub :=
    @uniformMeasure_isProbability ↥T ⊤ _ hTne_type hTpos
  have hval_meas : @Measurable ↥T X ⊤ _ Subtype.val :=
    fun _ _ => MeasurableSpace.measurableSet_top
  let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
  have hDprob : MeasureTheory.IsProbabilityMeasure D := by
    constructor; show D Set.univ = 1
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ]
    rw [Set.preimage_univ]; exact hD_sub_prob.measure_univ
  refine ⟨D, hDprob, ?_⟩
  -- The integral lower bound: ∫ EmpRad ∂(Measure.pi D) ≥ 1 / 2.
  --
  -- Key chain: Measure.pi D = (Measure.pi D_sub).map (val ∘ ·)  [by pi_map_pi]
  -- So ∫ EmpRad ∂(Measure.pi D) = ∫ ys, EmpRad(val ∘ ys) ∂(Measure.pi D_sub)  [by integral_map]
  -- On Fin m → ↥T (finite type), the integral is a weighted finite sum.
  -- EmpRad(val ∘ ys) = 1 when ys is injective (by empRad_eq_one_of_injective_in_shattered).
  -- EmpRad(val ∘ ys) ≥ 0 always (by empRad_nonneg).
  -- So ∫ ≥ P_sub[injective] ≥ 1 / 2 by birthday bound.
  --
  -- Step 1: Infrastructure for product measures.
  -- EmpRad = 1 on injective samples from T.
  have hEmpRad_inj : ∀ (ys : Fin m → ↥T), Function.Injective ys →
      EmpiricalRademacherComplexity X C (Subtype.val ∘ ys) = 1 := by
    intro ys h_inj
    exact empRad_eq_one_of_injective_in_shattered C hm T hT _
      (Subtype.val_injective.comp h_inj) (fun i => (ys i).property)
  -- EmpRad ≥ 0 everywhere.
  have hEmpRad_nn : ∀ xs : Fin m → X, 0 ≤ EmpiricalRademacherComplexity X C xs :=
    fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs
  -- EmpRad ≤ 1 everywhere.
  have hEmpRad_le : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 :=
    fun xs => empiricalRademacherComplexity_le_one X C hm xs
  -- The RademacherComplexity integral.
  -- We need: 1 / 2 ≤ ∫ EmpRad ∂(Measure.pi (fun _ => D)).
  -- By birthday probability: the fraction of injective tuples in T^m is ≥ 1 / 2.
  -- On injective tuples, EmpRad = 1. On non-injective, EmpRad ≥ 0.
  -- So the average ≥ (fraction injective) · 1 ≥ 1 / 2.
  --
  -- The formal connection between the Bochner integral and finite averaging
  -- on the product of a discrete probability measure requires:
  -- (a) pi_map_pi to relate product of pushforward to pushforward of product
  -- (b) integral_map to pull back the integral
  -- (c) integral lower bound via indicator function
  --
  -- We use the integral directly by bounding below with an indicator.
  change (1 : ℝ) / 2 ≤ RademacherComplexity X C D m
  unfold RademacherComplexity
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  have : MeasureTheory.IsProbabilityMeasure μ :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  -- Lower bound the integral.
  -- Define A = {xs | injective ∧ ∀ i, xs i ∈ T}. On A, EmpRad = 1. On Aᶜ, EmpRad ≥ 0.
  -- ∫ EmpRad ≥ ∫_A 1 = μ(A).toReal.
  -- Birthday bound: μ(A) ≥ 1 / 2.
  set A := { xs : Fin m → X | Function.Injective xs ∧ ∀ i, xs i ∈ T }
  -- EmpRad(xs) ≥ A.indicator(1)(xs) for all xs.
  have h_pointwise : ∀ xs : Fin m → X,
      A.indicator (fun _ => (1 : ℝ)) xs ≤ EmpiricalRademacherComplexity X C xs := by
    intro xs
    unfold Set.indicator; split
    · next hxs =>
      obtain ⟨h_inj, h_range⟩ := hxs
      exact le_of_eq (empRad_eq_one_of_injective_in_shattered C hm T hT xs h_inj h_range).symm
    · exact hEmpRad_nn xs
  -- A is measurable (the pi sigma-algebra on Fin m → X with MeasurableSingletonClass
  -- has all subsets measurable for finite Fin m, but we use a direct approach).
  have : MeasurableSingletonClass (Fin m → X) := Pi.instMeasurableSingletonClass
  have hA_meas : MeasurableSet A := by
    -- A ⊆ {xs | ∀ i, xs i ∈ T} which embeds into Fin m → ↑T, a finite type.
    -- So A is finite, hence measurable (finite union of measurable singletons).
    apply Set.Finite.measurableSet
    exact (Set.Finite.pi' (fun _ => T.finite_toSet)).subset (fun xs ⟨_, hr⟩ => hr)
  -- ∫ EmpRad ≥ μ(A).toReal via pullback to finite type Fin m → ↥T.
  -- On Fin m → ↥T (finite type), all functions are measurable/integrable automatically.
  -- We use MeasurableEmbedding.integral_map which requires no AEStronglyMeasurable on codomain.
  have : MeasurableSingletonClass (Fin m → ↥T) := Pi.instMeasurableSingletonClass
  let μ_sub : MeasureTheory.Measure (Fin m → ↥T) :=
    MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)
  have : MeasureTheory.IsProbabilityMeasure μ_sub :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  let φ : (Fin m → ↥T) → (Fin m → X) := fun ys i => Subtype.val (ys i)
  -- φ is a MeasurableEmbedding (injective, measurable, images of meas sets are meas).
  have hφ_emb : MeasurableEmbedding φ := by
    refine ⟨fun a b hab => funext (fun i => Subtype.val_injective (congr_fun hab i)),
      measurable_pi_iff.mpr (fun i => hval_meas.comp (measurable_pi_apply i)),
      fun s _ => ?_⟩
    -- φ '' s ⊆ {xs | ∀ i, xs i ∈ T} which is finite, so φ '' s is finite, hence measurable.
    apply Set.Finite.measurableSet
    apply (Set.Finite.pi' (fun _ => T.finite_toSet)).subset
    intro xs hxs
    obtain ⟨ys, _, rfl⟩ := hxs
    exact fun i => (ys i).property
  -- μ = μ_sub.map φ via pi_map_pi.
  have hμ_eq : μ = μ_sub.map φ := by
    simp only [μ, μ_sub, D, φ]
    exact (MeasureTheory.Measure.pi_map_pi (fun _ => hval_meas.aemeasurable)).symm
  -- Transfer integral via MeasurableEmbedding.integral_map (no AEStronglyMeasurable needed).
  have h_int_eq : ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ =
      ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
    conv_lhs => rw [hμ_eq]; exact hφ_emb.integral_map _
  -- Integrability of EmpRad ∘ φ on finite type (automatic: bounded, measurable_of_finite).
  have hf_sub_int : MeasureTheory.Integrable
      (fun ys => EmpiricalRademacherComplexity X C (φ ys)) μ_sub :=
    MeasureTheory.Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
      (MeasureTheory.ae_of_all _ (fun ys => by
        rw [Real.norm_of_nonneg (hEmpRad_nn _)]; exact hEmpRad_le _))
  -- Lower bound on the finite type.
  have h_int_bound : (μ A).toReal ≤ ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ := by
    rw [h_int_eq]
    set B := {ys : Fin m → ↥T | Function.Injective ys}
    have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
    have h_pw : ∀ ys : Fin m → ↥T,
        B.indicator (fun _ => (1 : ℝ)) ys ≤ EmpiricalRademacherComplexity X C (φ ys) := by
      intro ys; simp only [Set.indicator]; split
      · next hys => exact le_of_eq (hEmpRad_inj ys hys).symm
      · exact hEmpRad_nn _
    -- φ⁻¹'(A) ⊆ B: if φ ys is injective then ys is injective (Subtype.val is injective).
    have hA_le_B : μ A ≤ μ_sub B := by
      rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas]
      apply MeasureTheory.measure_mono
      intro ys (hys : φ ys ∈ A)
      change Function.Injective ys
      exact hys.1.of_comp
    calc (μ A).toReal
        ≤ (μ_sub B).toReal :=
          ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ_sub _) hA_le_B
      _ ≤ ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
          have h1 : ∫ ys, B.indicator (fun _ => (1 : ℝ)) ys ∂μ_sub = (μ_sub B).toReal := by
            rw [MeasureTheory.integral_indicator hB_meas,
              MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]; rfl
          linarith [MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ (fun ys =>
              Set.indicator_nonneg (fun _ _ => zero_le_one) ys))
            hf_sub_int
            (MeasureTheory.ae_of_all _ h_pw)]
  suffices h_birthday : (1 : ℝ) / 2 ≤ (μ A).toReal by linarith
  set B := {ys : Fin m → ↥T | Function.Injective ys}
  have hpre_eq : φ ⁻¹' A = B := by
    ext ys; constructor
    · intro (hys : φ ys ∈ A); exact hys.1.of_comp
    · intro (hys : Function.Injective ys)
      exact ⟨Subtype.val_injective.comp hys, fun i => (ys i).property⟩
  have hμA_eq_B : μ A = μ_sub B := by
    rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas, hpre_eq]
  rw [hμA_eq_B]
  simpa [μ_sub, D_sub, B] using
    uniform_injective_tuple_measure_half (α := ↥T) hTne_type m (by
      simpa [Fintype.card_coe] using hT_large)
