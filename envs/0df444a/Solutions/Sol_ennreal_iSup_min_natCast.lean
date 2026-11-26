-- Prove2me | solution 1 for ennreal_iSup_min_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:59.381794+00:00
-- url     : https://prove2.me/submissions/baaec670-c8db-4115-9e27-f4ed0aefe208

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral

set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
theorem _root_.solution (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne a ∞ with rfl | ha
  · have hmin : ∀ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) :=
      fun n => min_eq_right le_top
    calc (∞ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
      _ ≤ ⨆ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) :=
          iSup_mono fun n => (hmin n).symm.le
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (by simp [min_eq_left hn.le])
