-- Prove2me | solution 1 for volume_restrict_epigraph_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:00.200947+00:00
-- url     : https://prove2.me/submissions/42702ace-575d-43c7-abf3-acf12cc95f2e

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
theorem _root_.solution (t : ℝ≥0∞) (n : ℕ) :
    volume.restrict (Icc (0 : ℝ) n) {b : ℝ | t ≤ ENNReal.ofReal b}
      = (n : ℝ≥0∞) - min t (n : ℝ≥0∞) := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  rcases eq_or_ne t ∞ with rfl | ht
  · have hempty : {b : ℝ | (∞ : ℝ≥0∞) ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n = ∅ := by
      ext b
      simp [top_le_iff, ENNReal.ofReal_ne_top]
    rw [hempty]
    simp
  · have hinter : {b : ℝ | t ≤ ENNReal.ofReal b} ∩ Icc (0 : ℝ) n
        = Icc t.toReal n := by
      ext b
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨(ENNReal.le_ofReal_iff_toReal_le ht h2).mp h1, h3⟩
      · rintro ⟨h1, h2⟩
        have hb0 : (0 : ℝ) ≤ b := le_trans ENNReal.toReal_nonneg h1
        exact ⟨(ENNReal.le_ofReal_iff_toReal_le ht hb0).mpr h1, hb0, h2⟩
    rw [hinter, Real.volume_Icc]
    rcases le_or_gt t (n : ℝ≥0∞) with htn | htn
    · rw [min_eq_left htn, ← ENNReal.ofReal_natCast n,
        ← ENNReal.ofReal_toReal ht,
        ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal ht]
    · have hnt : (n : ℝ) < t.toReal := by
        rw [← ENNReal.toReal_natCast n]
        exact (ENNReal.toReal_lt_toReal (by finiteness) ht).mpr htn
      rw [min_eq_right htn.le, tsub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith)]
