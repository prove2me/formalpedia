-- Prove2me | solution 1 for pac_bayes_per_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:07.506842+00:00
-- url     : https://prove2.me/submissions/b6a1a790-83d3-4ae6-aaf4-e0f392c727f6

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PACBayes
public import Theorems.Thm_hoeffding_one_sided


set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Finset
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h₀ : H)
    (hbound_le_one : Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        TrueErrorReal X (hs h₀) c D >
          EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
          Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) }
      ≤ ENNReal.ofReal (P.prob h₀ * δ) := by
  -- Set up abbreviations
  set t := Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m))
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  -- Positivity facts
  have hPδ_pos : 0 < P.prob h₀ * δ := mul_pos (hP_pos h₀) hδ
  have h_inv_pos : 0 < 1 / (P.prob h₀ * δ) := div_pos one_pos hPδ_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have h_denom_pos : 0 < 2 * (↑m : ℝ) := by positivity
  have h_log_nonneg : 0 ≤ Real.log (1 / (P.prob h₀ * δ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPδ_pos]; simp only [one_mul]
    have h1 : P.prob h₀ ≤ 1 := by
      have := P.prob_sum_one
      calc P.prob h₀ ≤ ∑ h : H, P.prob h :=
            Finset.single_le_sum (fun i _ => P.prob_nonneg i) (Finset.mem_univ h₀)
        _ = 1 := P.prob_sum_one
    nlinarith
  have h_quot_nonneg : 0 ≤ Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) :=
    div_nonneg h_log_nonneg (le_of_lt h_denom_pos)
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  -- Handle the t = 0 case vs t > 0 case
  by_cases ht_pos_case : t = 0
  case pos =>
    have h_Pδ_ge_one : P.prob h₀ * δ ≥ 1 := by
      have ht_sq_zero : Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) = 0 := by
        rwa [Real.sqrt_eq_zero h_quot_nonneg] at ht_pos_case
      have h_log_zero : Real.log (1 / (P.prob h₀ * δ)) = 0 := by
        by_contra h_ne
        exact absurd (div_ne_zero h_ne (ne_of_gt h_denom_pos)) (not_not.mpr ht_sq_zero)
      have h_le : 1 / (P.prob h₀ * δ) ≤ 1 := by
        by_contra h_not_le
        push Not at h_not_le
        linarith [Real.log_pos h_not_le]
      have h_ge : 1 ≤ 1 / (P.prob h₀ * δ) := by
        by_contra h_not_ge
        push Not at h_not_ge
        have := Real.log_neg (by linarith [h_inv_pos]) h_not_ge
        linarith [h_log_nonneg]
      have h_inv_eq_one : 1 / (P.prob h₀ * δ) = 1 := le_antisymm h_le h_ge
      rw [div_eq_one_iff_eq (ne_of_gt hPδ_pos)] at h_inv_eq_one; linarith
    calc μ { S | TrueErrorReal X (hs h₀) c D >
            EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t }
        ≤ μ Set.univ := μ.mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (P.prob h₀ * δ) := ENNReal.ofReal_le_ofReal h_Pδ_ge_one
  case neg =>
    -- t > 0 case: use Hoeffding
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_pos_case)
    -- The event {TrueErr > EmpErr + t} ⊆ {EmpErr ≤ TrueErr - t}
    have h_sub : { S : Fin m → X |
        TrueErrorReal X (hs h₀) c D >
          EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i))) (zeroOneLoss Bool) + t }
      ⊆ { xs : Fin m → X | EmpiricalError X Bool (hs h₀) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool) ≤ TrueErrorReal X (hs h₀) c D - t } := by
      intro xs hxs
      simp only [Set.mem_ofPred_eq] at hxs ⊢
      linarith
    -- Measurability for Hoeffding
    have hmeas : MeasurableSet {x : X | hs h₀ x ≠ c x} :=
      (measurableSet_eq_fun (hhs_meas h₀) hc_meas).compl
    -- Apply hoeffding_one_sided
    have h_hoeff := hoeffding_one_sided D (hs h₀) c m hm t ht_pos hbound_le_one hmeas
    -- Key calculation: exp(-2·m·t²) = P(h₀)·δ
    have h_tsq : t ^ 2 = Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m) := by
      rw [sq, ← Real.sqrt_mul h_quot_nonneg, Real.sqrt_mul_self h_quot_nonneg]
    have h_exp_eq : Real.exp (-2 * ↑m * t ^ 2) = P.prob h₀ * δ := by
      rw [h_tsq]
      rw [show -2 * ↑m * (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) =
            -Real.log (1 / (P.prob h₀ * δ)) from by field_simp]
      rw [Real.exp_neg, Real.exp_log h_inv_pos]
      field_simp
    calc μ { S | TrueErrorReal X (hs h₀) c D >
            EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t }
        ≤ μ { xs | EmpiricalError X Bool (hs h₀) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool) ≤ TrueErrorReal X (hs h₀) c D - t } := μ.mono h_sub
      _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := h_hoeff
      _ = ENNReal.ofReal (P.prob h₀ * δ) := by rw [h_exp_eq]
