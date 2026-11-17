-- Prove2me | solution 1 for finite_clock_guarded_continuous_kernel_local
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:45:53.750038+00:00
-- url     : https://prove2.me/submissions/792a7001-63ce-4340-9be5-02e48cb44e2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem finite_clock_guarded_continuous_kernel_local
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (Y : ℝ≥0 → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0) :
    Integrable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set F : ℝ → ℝ := (Icc a b).piecewise f (fun _ => 0) with hF
  have hFm : Measurable F := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have heq : (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0)
      = fun t => if t ≤ τ ∧ Y t ∈ Icc a b then Real.exp (-(q * (t : ℝ))) * F (Y t) else 0 := by
    funext t
    split_ifs with h
    · rw [hF, Set.piecewise_eq_of_mem _ _ _ h.2]
    · rfl
  rw [heq]
  have hmeas : Measurable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * F (Y t) else 0) := by
    refine Measurable.ite (measurableSet_Iic.inter (hY measurableSet_Icc)) ?_ measurable_const
    exact (Real.measurable_exp.comp ((measurable_const.mul measurable_subtype_coe).neg)).mul
      (hFm.comp hY)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (max C 0)
    (Filter.Eventually.of_forall fun t => ?_)

  split_ifs with h
  · rw [norm_mul]
    have h1 : ‖Real.exp (-(q * (t : ℝ)))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq t.2))
    have h2 : ‖F (Y t)‖ ≤ max C 0 := by
      rw [hF, Set.piecewise_eq_of_mem _ _ _ h.2]
      exact (hC _ h.2).trans (le_max_left _ _)
    calc _ ≤ 1 * max C 0 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = max C 0 := one_mul _
  · simp

theorem solution
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (Y : ℝ≥0 → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0) :
    Integrable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set F : ℝ → ℝ := (Icc a b).piecewise f (fun _ => 0) with hF
  have hFm : Measurable F := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  have heq : (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0)
      = fun t => if t ≤ τ ∧ Y t ∈ Icc a b then Real.exp (-(q * (t : ℝ))) * F (Y t) else 0 := by
    funext t
    split_ifs with h
    · rw [hF, Set.piecewise_eq_of_mem _ _ _ h.2]
    · rfl
  rw [heq]
  have hmeas : Measurable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * F (Y t) else 0) := by
    refine Measurable.ite (measurableSet_Iic.inter (hY measurableSet_Icc)) ?_ measurable_const
    exact (Real.measurable_exp.comp ((measurable_const.mul measurable_subtype_coe).neg)).mul
      (hFm.comp hY)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (max C 0)
    (Filter.Eventually.of_forall fun t => ?_)

  split_ifs with h
  · rw [norm_mul]
    have h1 : ‖Real.exp (-(q * (t : ℝ)))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq t.2))
    have h2 : ‖F (Y t)‖ ≤ max C 0 := by
      rw [hF, Set.piecewise_eq_of_mem _ _ _ h.2]
      exact (hC _ h.2).trans (le_max_left _ _)
    calc _ ≤ 1 * max C 0 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = max C 0 := one_mul _
  · simp

end

