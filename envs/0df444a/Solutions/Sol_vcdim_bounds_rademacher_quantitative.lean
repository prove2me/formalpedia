-- Prove2me | solution 1 for vcdim_bounds_rademacher_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:07.482796+00:00
-- url     : https://prove2.me/submissions/059dc9f1-5fac-480d-a0f5-1391a673f42b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_boolToSign_abs_eq_one
public import Theorems.Thm_rademacherCorrelation_abs_le_one
public import Theorems.Thm_empiricalRademacherComplexity_le_one
public import Theorems.Thm_rademacher_mgf_bound
public import Theorems.Thm_finite_massart_lemma
public import Theorems.Thm_sum_choose_le_exp_pow
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
private theorem ncard_restrictions_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (S : Finset X) (d : ℕ)
    (hvc : VCDim X C = ↑d) :
    ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  classical
  -- The restriction set is finite since ↥S → Bool is Fintype
  set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } with hR_def
  have hR_fin : R.Finite := Set.Finite.subset (Set.finite_univ) (Set.subset_univ _)
  -- Convert to Finset for counting
  rw [Set.ncard_eq_toFinset_card']
  -- Build a Finset family AA : Finset (Finset ↥S) from R
  set R_fin := R.toFinset with hR_fin_def
  set AA := R_fin.image (fun f => Finset.univ.filter (fun x => f x = true)) with hAA_def
  -- Step 1: R_fin.card ≤ AA.card (the map f ↦ filter is injective on Bool-valued functions)
  have h_inj : Function.Injective
      (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
    intro f g hfg
    funext x
    have := Finset.ext_iff.mp hfg x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  have h1 : R_fin.card = AA.card := by
    rw [hAA_def]; exact (Finset.card_image_of_injective _ h_inj).symm
  -- Step 2: AA.card ≤ AA.shatterer.card (Mathlib: card_le_card_shatterer)
  have h2 : AA.card ≤ AA.shatterer.card := Finset.card_le_card_shatterer AA
  -- Step 3: AA.shatterer.card ≤ ∑ k ∈ Iic AA.vcDim, C(Fintype.card ↥S, k)
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ AA
  -- Step 4: vcDim(AA) ≤ d
  -- If AA shatters T, then C shatters T.map Subtype.val, so |T| ≤ d
  have h4 : AA.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT
    have hTs : AA.Shatters T := Finset.mem_shatterer.mp hT
    -- If AA shatters T ⊆ ↥S, then C shatters T.map Subtype.val ⊆ X
    set Tval := T.map ⟨Subtype.val, Subtype.val_injective⟩ with hTval_def
    suffices hShats : Shatters X C Tval by
      have hCard : Tval.card = T.card := Finset.card_map _
      have : (Tval.card : WithTop ℕ) ≤ ↑d := by
        calc (Tval.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) _ hShats
          _ = ↑d := hvc
      linarith [WithTop.coe_le_coe.mp this, hCard]
    -- Prove Shatters X C Tval: for any labeling g : ↥Tval → Bool, find c ∈ C matching
    intro g
    -- Helper function: extend g to ↥S via dite
    let g' : ↥S → Bool := fun x =>
      if h : (↑x : X) ∈ Tval then g ⟨↑x, h⟩ else false
    -- Build t_sub ⊆ T: elements labeled true
    let t_sub : Finset ↥S := T.filter (fun x => g' x = true)
    have ht_sub : t_sub ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA, hTA⟩ := hTs ht_sub
    simp only [hAA_def, Finset.mem_image] at hA
    obtain ⟨f, hf_mem, rfl⟩ := hA
    rw [Set.mem_toFinset] at hf_mem
    obtain ⟨c, hcC, hcf⟩ := hf_mem
    refine ⟨c, hcC, ?_⟩
    intro ⟨y, hyTval⟩
    -- c ↑(y, hyTval) = c y. Need to match this with g ⟨y, hyTval⟩.
    -- y ∈ Tval, so ∃ x ∈ T, ↑x = y
    have hyTval' := hyTval
    rw [hTval_def, Finset.mem_map] at hyTval'
    obtain ⟨⟨y', hy'S⟩, hy'T, hy'eq⟩ := hyTval'
    -- hy'eq : ↑⟨y', hy'S⟩ = y, i.e., y' = y
    simp only [Function.Embedding.coeFn_mk] at hy'eq
    subst hy'eq
    -- Now y = y', hyTval : y' ∈ Tval, hy'S : y' ∈ S, hy'T : ⟨y', hy'S⟩ ∈ T
    have hcf_y := hcf ⟨y', hy'S⟩
    -- hcf_y : c y' = f ⟨y', hy'S⟩
    -- From hTA: T ∩ filter(f · = true) = t_sub = T.filter(g' · = true)
    have h_f_iff_g' : f ⟨y', hy'S⟩ = true ↔ g' ⟨y', hy'S⟩ = true := by
      have h1 : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) ↔
          f ⟨y', hy'S⟩ = true := by
        simp [Finset.mem_inter, Finset.mem_filter, hy'T]
      have h2 : (⟨y', hy'S⟩ : ↥S) ∈ t_sub ↔ g' ⟨y', hy'S⟩ = true := by
        simp [t_sub, Finset.mem_filter, hy'T]
      rw [hTA] at h1
      exact h1.symm.trans h2
    -- g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ since y' ∈ Tval
    have h_g'_eq : g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by
      simp only [g', dif_pos hyTval]
    -- Combine: c y' = f ⟨y',hy'S⟩ and f = true ↔ g = true
    rw [hcf_y, ← h_g'_eq]
    exact Bool.eq_iff_iff.mpr h_f_iff_g'
  -- Step 5: Fintype.card ↥S = S.card
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  -- Combine
  calc R.toFinset.card
      = AA.card := h1
    _ ≤ AA.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic AA.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic AA.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h4
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        rw [Nat.range_succ_eq_Iic]
private theorem conceptClass_nonempty_of_vcdim_eq_pos {X : Type u}
    (C : ConceptClass X Bool) {d : ℕ} (hd : VCDim X C = ↑d) (hd_pos : 0 < d) :
    C.Nonempty := by
  by_contra hC_empty
  rw [Set.not_nonempty_iff_eq_empty] at hC_empty
  have : VCDim X C = 0 := by
    simp only [VCDim]
    apply le_antisymm
    · apply iSup₂_le; intro S hS
      exfalso; unfold Shatters at hS
      simp_all
    · exact bot_le
  simp_all
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    (d : ℕ) (hd : VCDim X C = ↑d) (hd_pos : 0 < d) (hdm : d ≤ m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ Real.sqrt (2 * d * Real.log (Real.exp 1 * ↑m / d) / m) := by
  set B := Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m)
  suffices h_pw : ∀ (xs : Fin m → X), EmpiricalRademacherComplexity X C xs ≤ B by
    unfold RademacherComplexity
    calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
        ≤ ∫ _xs, B ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact MeasureTheory.ae_of_all _
              (fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
          · exact MeasureTheory.integrable_const B
          · exact MeasureTheory.ae_of_all _ h_pw
      _ = B := by simp [MeasureTheory.integral_const]
  -- Pointwise bound: Massart + Sauer-Shelah.
  intro xs
  by_cases hB1 : 1 ≤ B
  · exact le_trans (empiricalRademacherComplexity_le_one X C hm xs) hB1
  · -- B < 1: genuine Massart-Sauer content.
    push Not at hB1
    -- MASSART FINITE LEMMA + SAUER-SHELAH CHAIN
    -- Proof: EmpRad(xs) ≤ √(2d·log(em/d)/m) = B when B < 1
    classical
    -- Positivity facts
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have hcard_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := SignVector m)
    have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
    -- C is nonempty (from VCDim ≥ 1)
    have hC_ne : C.Nonempty := conceptClass_nonempty_of_vcdim_eq_pos C hd hd_pos
    obtain ⟨h₀, hh₀⟩ := hC_ne
    -- === STEP 1: Restriction collapse ===
    -- The correlation depends on h only through fun i => h(xs i)
    -- dpats = distinct restriction patterns of C on xs
    let dpats : Finset (Fin m → Bool) :=
        Finset.univ.filter (fun p => ∃ h ∈ C, ∀ i, h (xs i) = p i)
    have hdpats_ne : dpats.Nonempty := by
      refine ⟨fun i => h₀ (xs i), ?_⟩
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h₀, hh₀, fun _ => rfl⟩
    -- rademacherCorrelation h σ xs = corr_pat (fun i => h(xs i)) σ
    -- where corr_pat p σ = (1/m) ∑ boolToSign(σ i) * boolToSign(p i)
    -- For each σ: sSup { corr(h,σ,xs) | h ∈ C } ≤ dpats.sup' (corr_pat(·, σ))
    -- Abbreviation for the sup' function
    set cf : SignVector m → (Fin m → Bool) → ℝ :=
      fun σ p => (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (p i)
    have h_corr_eq : ∀ (h : Concept X Bool) (σ : SignVector m),
        rademacherCorrelation h σ xs = cf σ (fun i => h (xs i)) := by
      intro h σ; unfold rademacherCorrelation
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
    have h_mem_dpats : ∀ h ∈ C, (fun i => h (xs i)) ∈ dpats := by
      intro h hh
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h, hh, fun _ => rfl⟩
    have h_ssup_le_sup' : ∀ σ : SignVector m,
        sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
        dpats.sup' hdpats_ne (cf σ) := by
      intro σ
      apply csSup_le
      · exact ⟨rademacherCorrelation h₀ σ xs, h₀, hh₀, rfl⟩
      · rintro r ⟨h, hh, rfl⟩
        rw [h_corr_eq]
        exact Finset.le_sup' (cf σ) (h_mem_dpats h hh)
    -- EmpRad ≤ (1/card) * ∑_σ dpats.sup' ...
    have h_empRad_le : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, dpats.sup' hdpats_ne (cf σ) := by
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt h1card_pos)
      exact Finset.sum_le_sum (fun σ _ => h_ssup_le_sup' σ)
    -- === STEP 2: Index dpats by Fin N and apply Massart ===
    set N := dpats.card
    have hN_pos : 0 < N := Finset.Nonempty.card_pos hdpats_ne
    -- Use Fintype.equivFin on the subtype { p // p ∈ dpats }
    have hcard_dpats : Fintype.card { p // p ∈ dpats } = N := Fintype.card_coe dpats
    let e : { p // p ∈ dpats } ≃ Fin N :=
      hcard_dpats ▸ Fintype.equivFin _
    -- Define Z : Fin N → SignVector m → ℝ
    let Z : Fin N → SignVector m → ℝ :=
      fun j σ => cf σ (e.symm j).val
    -- dpats.sup' (cf σ) = univ.sup' (fun j => Z j σ)
    have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
    have h_sup'_eq : ∀ σ : SignVector m,
        dpats.sup' hdpats_ne (cf σ) =
        Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
      intro σ
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        intro p hp
        exact Finset.le_sup'_of_le (f := fun j => Z j σ) (Finset.mem_univ (e ⟨p, hp⟩))
          (by
            change cf σ p ≤ cf σ (e.symm (e ⟨p, hp⟩)).val
            simp [Equiv.symm_apply_apply])
      · rw [Finset.sup'_le_iff]
        intro j _
        exact Finset.le_sup' (cf σ) (e.symm j).prop
    -- Rewrite
    have h_empRad_le2 : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
      simp_all
    -- === MGF bound for each Z_j ===
    set σ_param := (1 : ℝ) / Real.sqrt m
    have hσ_pos : 0 < σ_param := by positivity
    have h_mgf_Z : ∀ j : Fin N, ∀ t : ℝ, 0 ≤ t →
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
        Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      intro j t ht
      -- Z j sv = cf sv (e.symm j).val = (1/m) * ∑ boolToSign(sv i) * boolToSign(p i)
      set p := (e.symm j).val with hp_def
      -- Apply rademacher_mgf_bound with a_i = boolToSign(p i), c = 1
      have h_bound := rademacher_mgf_bound hm (fun i => boolToSign (p i)) 1 (by norm_num)
        (fun i => le_of_eq (boolToSign_abs_eq_one (p i))) t ht
      -- Z j sv = (1/m) * ∑ boolToSign(sv i) * boolToSign(p i)
      --       = (1/m) * ∑ boolToSign(p i) * boolToSign(sv i) (by mul_comm)
      have h_Z_rewrite : ∀ sv, Z j sv =
          (1 / (m : ℝ)) * ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i) := by
        intro sv
        change cf sv p = _
        simp only [cf]
        congr 1; apply Finset.sum_congr rfl; intro i _; ring
      -- Rewrite LHS to match h_bound
      have h_lhs_eq : ∀ sv, Real.exp (t * Z j sv) =
          Real.exp
            (t * ((1 / (m : ℝ)) * ∑ i,
              (fun i => boolToSign (p i)) i * boolToSign (sv i))) := by
        intro sv; rw [h_Z_rewrite]
      simp_rw [h_lhs_eq]
      -- RHS: σ_param² = 1/m, so t²·σ_param²/2 = t²·1²/(2m)
      have h_rhs_eq : t ^ 2 * σ_param ^ 2 / 2 = t ^ 2 * 1 ^ 2 / (2 * ↑m) := by
        rw [one_pow, mul_one, show σ_param = 1 / Real.sqrt ↑m from rfl]
        rw [one_div, inv_pow, Real.sq_sqrt (le_of_lt hm_pos)]
        ring
      simp_all
    -- Apply finite_massart_lemma
    have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
    have h_massart := finite_massart_lemma hm hN_pos Z σ_param hσ_pos h_mgf_Z
    -- === STEP 3: Bound N via Sauer-Shelah ===
    set S := Finset.univ.image xs
    have h_dpats_card_le : (N : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
      -- Injection from dpats to {f : S → Bool | ∃ c ∈ C, ∀ x, c x = f x}
      -- then ncard_restrictions ≤ ∑ choose ≤ (em/d)^d
      set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
      -- dpats maps into R via the restriction map
      have h_dpats_mem : ∀ p ∈ dpats, ∃ c ∈ C, ∀ i, c (xs i) = p i := by
        intro p hp
        have := Finset.mem_filter.mp hp
        exact this.2
      have h_inj_card : N ≤ R.toFinset.card := by
        -- Map: p ↦ (fun x => p (choose_index x))
        -- where for x ∈ S, choose_index x is some i with xs i = x
        apply Finset.card_le_card_of_injOn
          (fun (p : Fin m → Bool) (x : ↥S) =>
            p ((Finset.mem_image.mp x.prop).choose))
          -- maps into R.toFinset
          (fun p hp => by
            obtain ⟨c, hcC, hc_agree⟩ := h_dpats_mem p hp
            have : (fun (x : ↥S) => p ((Finset.mem_image.mp x.prop).choose)) ∈ R := by
              exact ⟨c, hcC, fun ⟨x, hx⟩ => by
                have hcs := (Finset.mem_image.mp hx).choose_spec
                -- hcs.2 : xs(choose) = x, so c x = c(xs(choose)) = p(choose)
                change c x = p ((Finset.mem_image.mp hx).choose)
                conv_lhs => rw [← hcs.2]
                exact hc_agree _⟩
            exact Set.mem_toFinset.mpr this)
          -- injective on dpats
          (fun p₁ hp₁ p₂ hp₂ heq => by
            obtain ⟨c₁, _, hc₁⟩ := h_dpats_mem p₁ hp₁
            obtain ⟨c₂, _, hc₂⟩ := h_dpats_mem p₂ hp₂
            funext i
            have hxi_in : xs i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            have hcs := (Finset.mem_image.mp hxi_in).choose_spec
            have h_at := congr_fun heq ⟨xs i, hxi_in⟩
            -- p₁ i = c₁(xs i) and p₁(choose) = c₁(xs(choose)) = c₁(xs i)
            -- Similarly for p₂. And h_at says p₁(choose) = p₂(choose).
            rw [← hc₁ i, ← hc₂ i]
            -- c₁(xs i) = c₁(xs(choose)) by hcs.2 : xs(choose) = xs i
            rw [← hcs.2]
            -- Need: c₁(xs(choose)) = c₂(xs(choose))
            -- = p₁(choose) by hc₁, = p₂(choose) by h_at, = c₂(xs(choose)) by hc₂
            rw [hc₁, hc₂]
            exact h_at)
      have h_ncard_le := ncard_restrictions_le_sum_choose_set C S d hd
      have hS_card_le : S.card ≤ m := by
        calc (Finset.univ.image xs).card ≤ Finset.univ.card := Finset.card_image_le
          _ = m := by simp
      have h_exp := sum_choose_le_exp_pow d m hd_pos hdm
      calc (N : ℝ)
          ≤ ↑R.toFinset.card := by exact_mod_cast h_inj_card
        _ = ↑R.ncard := by rw [Set.ncard_eq_toFinset_card']
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose S.card i) := by exact_mod_cast h_ncard_le
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
            push_cast
            apply Finset.sum_le_sum
            intro i _
            exact_mod_cast Nat.choose_le_choose i hS_card_le
        _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by push_cast at h_exp ⊢; exact h_exp
    -- === STEP 4: Combine ===
    have h_emd_ge_one : (1 : ℝ) ≤ Real.exp 1 * ↑m / ↑d := by
      rw [le_div_iff₀ hd_pos_r]
      have : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have hdm_r : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
      nlinarith
    have h_log_emd_nonneg : 0 ≤ Real.log (Real.exp 1 * ↑m / ↑d) :=
      Real.log_nonneg h_emd_ge_one
    have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have h_log_N_le : Real.log ↑N ≤ ↑d * Real.log (Real.exp 1 * ↑m / ↑d) := by
      calc Real.log ↑N
          ≤ Real.log ((Real.exp 1 * ↑m / ↑d) ^ d) :=
            Real.log_le_log hN_real_pos h_dpats_card_le
        _ = ↑d * Real.log (Real.exp 1 * ↑m / ↑d) := by rw [Real.log_pow]
    calc EmpiricalRademacherComplexity X C xs
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := h_empRad_le2
      _ ≤ σ_param * Real.sqrt (2 * Real.log ↑N) := h_massart
      _ ≤ σ_param * Real.sqrt (2 * (↑d * Real.log (Real.exp 1 * ↑m / ↑d))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_pos)
          apply Real.sqrt_le_sqrt; nlinarith [h_log_N_le]
      _ = Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := by
          -- (1/√m) * √(2d·log(em/d)) = √((2d·log(em/d))/m)
          rw [show 2 * (↑d * Real.log (Real.exp 1 * ↑m / ↑d)) =
              2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) by ring]
          rw [show σ_param = 1 / Real.sqrt ↑m from rfl]
          rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hm_pos))]
          congr 1; rw [inv_mul_eq_div]
      _ = B := rfl
