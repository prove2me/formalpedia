-- Prove2me | solution 1 for exchangeability_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:44.390418+00:00
-- url     : https://prove2.me/submissions/1ac6297e-426e-4782-b8fd-a8dfde128a05

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_restriction_pattern_count
public import Theorems.Thm_finite_exchangeability_bound
public import Theorems.Thm_rademacher_mgf_bound

section
@[expose] public section
universe u v
open MeasureTheory ENNReal
private theorem rademacher_markov_filter_bound {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    ((Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) ≤
    (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set t₀ := (m : ℝ) * ε / 2 with ht₀_def
  have ht₀_pos : 0 < t₀ := by positivity
  have ht₀_nn : 0 ≤ t₀ := ht₀_pos.le
  have h_mgf := rademacher_mgf_bound hm a 1 zero_le_one (fun i => ha i) t₀ ht₀_nn
  have h_filter_le : ∀ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
      Real.exp (t₀ * (ε / 2)) ≤
      Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
    intro σ hσ
    simp only [Finset.mem_filter] at hσ
    exact Real.exp_le_exp_of_le (by nlinarith [hσ.2])
  have h_sum_filter : (Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card *
      Real.exp (t₀ * (ε / 2)) ≤
      ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
        (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h_filter_le
  have h_filter_sub_all :
      ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
        (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
      ∑ σ : SignVector m,
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun σ _ _ => (Real.exp_pos _).le)
  have hSV_pos : (0 : ℝ) < Fintype.card (SignVector m) := Nat.cast_pos.mpr Fintype.card_pos
  set filt := Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2) with hfilt_def
  have h_all_sum_bound : ∑ σ : SignVector m,
      Real.exp (t₀ * ((1 / ↑m) * ∑ i, a i * boolToSign (σ i))) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) := by
    have hSV_ne : (Fintype.card (SignVector m) : ℝ) ≠ 0 := ne_of_gt hSV_pos
    have := mul_le_mul_of_nonneg_left h_mgf (le_of_lt hSV_pos)
    rwa [← mul_assoc, mul_one_div_cancel hSV_ne, one_mul] at this
  have h_chain : (filt.card : ℝ) * Real.exp (t₀ * (ε / 2)) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) :=
    (h_sum_filter.trans h_filter_sub_all).trans h_all_sum_bound
  have h_exp_pos : 0 < Real.exp (t₀ * (ε / 2)) := Real.exp_pos _
  have h_card_le : (filt.card : ℝ) ≤
      (Fintype.card (SignVector m) : ℝ) *
      Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
    le_div_iff₀ h_exp_pos |>.mpr h_chain
  calc (filt.card : ℝ) ≤ (Fintype.card (SignVector m) : ℝ) *
          Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
        h_card_le
    _ = (Fintype.card (SignVector m) : ℝ) *
          (Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2))) := by
        ring
    _ = (Fintype.card (SignVector m) : ℝ) *
          Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m) - t₀ * (ε / 2)) := by
        congr 1; rw [Real.exp_sub]
    _ = (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        congr 1; rw [ht₀_def]; field_simp; ring_nf
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (_hmeas_C : ∀ h ∈ C, Measurable h) (_hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (_hε2 : ε ≤ 2) (_hC : C.Nonempty)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  intro μ
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hbound_def
  have hbound_nonneg : 0 ≤ bound := mul_nonneg (Nat.cast_nonneg' _) (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hE_def
  by_cases h_triv : 1 ≤ bound
  · -- Case 1: bound ≥ 1, so probability ≤ 1 ≤ bound
    have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := inferInstance
    calc (μ.prod μ) E
        ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
  · -- Case 2: bound < 1
    push Not at h_triv
    classical
    set ν := MeasureTheory.Measure.pi (fun _ : Fin m => D.prod D) with hν_def
    set eqv := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
    have h_mp : MeasurePreserving (⇑eqv) ν (μ.prod μ) := by
      rw [hν_def]
      exact measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
    have h_meas_eq : (μ.prod μ) E = ν (eqv ⁻¹' E) := by rw [← h_mp.map_eq]; exact eqv.map_apply E
    rw [h_meas_eq]
    let swap_fun (σ : SignVector m) : (Fin m → X × X) → (Fin m → X × X) :=
      fun z i => if σ i then (z i).swap else z i
    have h_swap_meas : ∀ σ, Measurable (swap_fun σ) := by
      intro σ; apply measurable_pi_iff.mpr; intro i
      by_cases hσi : σ i
      · simp only [swap_fun, hσi, ↓reduceIte]
        exact (measurable_pi_apply i |>.snd).prod (measurable_pi_apply i |>.fst)
      · simp only [swap_fun, hσi]
        exact measurable_pi_apply i
    have h_swap_pres : ∀ σ, ν.map (swap_fun σ) = ν := by
      intro σ; rw [hν_def]
      let f_σ : Fin m → (X × X) → (X × X) := fun i => if σ i then Prod.swap else id
      have h_eq_pointwise : swap_fun σ = fun z i => f_σ i (z i) := by
        funext z; funext i; simp only [swap_fun, f_σ]; split <;> simp
      rw [h_eq_pointwise]
      rw [MeasureTheory.Measure.pi_map_pi (fun i => by
        simp only [f_σ]; split
        · exact measurable_swap.aemeasurable
        · exact measurable_id.aemeasurable)]
      congr 1; funext i; simp only [f_σ]
      split
      · exact MeasureTheory.Measure.prod_swap (μ := D) (ν := D)
      · exact MeasureTheory.Measure.map_id
    set S := eqv ⁻¹' E
    have h_per_z_bound : ∀ z : Fin m → X × X,
        ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ≥0∞)
        ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
            (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
      intro z
      let merged : Fin (2 * m) → X := fun j =>
        if h : j.val < m then (z ⟨j.val, by omega⟩).1
        else (z ⟨j.val - m, by omega⟩).2
      have h_pattern_count :=
        restriction_pattern_count (X := X) (C := C) (c := c) (n := 2 * m) (z := merged)
      have h_markov_bound : ∀ (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
          ((Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) ≤
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) :=
        rademacher_markov_filter_bound hm hε
      have h_bound_real : ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ) ≤
          (↑(GrowthFunction X C (2 * m)) : ℝ) *
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        let PatternSet := {p : Fin (2 * m) → Bool |
          ∃ h ∈ C, ∀ i, p i = decide (h (merged i) ≠ c (merged i))}
        have hPS_finite : PatternSet.Finite := Set.toFinite PatternSet
        let PS := hPS_finite.toFinset
        have hPS_card : PS.card ≤ GrowthFunction X C (2 * m) := by
          rw [show PS.card = PatternSet.ncard from
            (Set.ncard_eq_toFinset_card PatternSet hPS_finite).symm]
          exact h_pattern_count
        let patToCoeff (p : Fin (2 * m) → Bool) : Fin m → ℝ := fun i =>
          -((if p (⟨i.val + m, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0) -
            (if p (⟨i.val, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0))
        have h_ptc_bound : ∀ p : Fin (2 * m) → Bool, ∀ i : Fin m, |patToCoeff p i| ≤ 1 := by
          intro p i; simp only [patToCoeff, abs_neg]
          split <;> split <;> simp
        have h_gap_identity : ∀ (h : X → Bool) (σ : SignVector m),
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).2 i)) (c ((eqv (swap_fun σ z)).2 i))) -
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).1 i)) (c ((eqv (swap_fun σ z)).1 i))) =
            ∑ i : Fin m,
              patToCoeff (fun j => decide (h (merged j) ≠ c (merged j))) i *
              boolToSign (σ i) := by
          intro h σ
          rw [← Finset.sum_sub_distrib]
          congr 1; ext i
          simp only [eqv, swap_fun, patToCoeff, merged,
            MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
            MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
          have hi_lt : i.val < m := i.isLt
          have hi_plus_ge : ¬(i.val + m < m) := by omega
          have him : i.val + m - m = i.val := by omega
          simp only [hi_lt, ↓reduceDIte, hi_plus_ge, him]
          rcases Bool.eq_false_or_eq_true (σ i) with hσi | hσi <;> simp only [hσi]
          · -- σ i = false: not swapped, .2 = (z i).2, .1 = (z i).1
            simp only [boolToSign, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
          · -- σ i = true: swapped, .2 = (z i).1, .1 = (z i).2
            simp only [boolToSign, Prod.swap, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
        have h_filter_biUnion :
            Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S) ⊆
            PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
              (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)) := by
          intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
          have hσS : swap_fun σ z ∈ S := hσ
          simp only [S, Set.mem_preimage, hE_def, Set.mem_ofPred_eq] at hσS
          obtain ⟨h, hC_h, hgap⟩ := hσS
          let p : Fin (2 * m) → Bool := fun j => decide (h (merged j) ≠ c (merged j))
          apply Finset.mem_biUnion.mpr
          refine ⟨p, hPS_finite.mem_toFinset.mpr ⟨h, hC_h, fun i => rfl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          have h_gid := h_gap_identity h σ
          simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hgap
          rw [div_sub_div_same] at hgap
          change (1 : ℝ) / ↑m * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2
          simp only [p] at hgap ⊢
          simpa [h_gid, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hgap
        have hexp_nn : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
        calc ((Finset.univ.filter (fun σ : SignVector m =>
                swap_fun σ z ∈ S)).card : ℝ)
            ≤ ((PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card h_filter_biUnion
          _ ≤ ∑ p ∈ PS, ((Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ PS,
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
              Finset.sum_le_sum (fun p _ => h_markov_bound (patToCoeff p) (h_ptc_bound p))
          _ = (PS.card : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (↑(GrowthFunction X C (2 * m)) : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast hPS_card
              · exact mul_nonneg (Nat.cast_nonneg' _) hexp_nn
          _ = (↑(GrowthFunction X C (2 * m)) : ℝ) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by ring
      exact_mod_cast ENNReal.ofReal_le_ofReal h_bound_real
    have hS_nullmeas : MeasureTheory.NullMeasurableSet S ν :=
      (hE_nullmeas.preimage h_mp.quasiMeasurePreserving)
    have h_swap_mp : ∀ σ : SignVector m, MeasureTheory.MeasurePreserving (swap_fun σ) ν ν :=
      fun σ => ⟨h_swap_meas σ, h_swap_pres σ⟩
    have h_pointwise : ∀ z : Fin m → X × X,
        (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z)
        ≤ ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
      intro z
      have h_sum_eq_card : (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z) =
          ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal) := by
        simp only [Set.indicator_apply, Pi.one_apply, Set.mem_preimage]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h_sum_eq_card]
      calc ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal)
          ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
            h_per_z_bound z
        _ = ENNReal.ofReal (bound * (Fintype.card (SignVector m) : ℝ)) := by
            congr 1; rw [hbound_def]; ring
        _ = ENNReal.ofReal bound * ENNReal.ofReal (Fintype.card (SignVector m) : ℝ) := by
            rw [ENNReal.ofReal_mul hbound_nonneg]
        _ = ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
            congr 1; rw [ENNReal.ofReal_natCast]
    exact finite_exchangeability_bound swap_fun S h_swap_mp hS_nullmeas
      (ENNReal.ofReal bound) h_pointwise
