-- Prove2me | solution 1 for ennreal_le_iff_forall_lt_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:24.081029+00:00
-- url     : https://prove2.me/submissions/3959e755-48b7-4525-b213-04e7aca3d63b

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
theorem _root_.solution {a q : ℝ≥0∞} (hq : q ≠ ∞) :
    a ≤ q ↔ ∀ k : ℕ, a < q + ((k : ℝ≥0∞) + 1)⁻¹ := by
  constructor
  · intro h k
    exact lt_of_le_of_lt h
      (ENNReal.lt_add_right hq (ENNReal.inv_ne_zero.mpr (by finiteness)))
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε0, hεa⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hlt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt
      (show (ε : ℝ≥0∞) ≠ 0 from by exact_mod_cast hε0.ne')
    have h1 : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
      le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.mpr le_self_add) hk)
    exact absurd (h k) (not_lt.mpr (le_trans (by gcongr) hεa.le))
