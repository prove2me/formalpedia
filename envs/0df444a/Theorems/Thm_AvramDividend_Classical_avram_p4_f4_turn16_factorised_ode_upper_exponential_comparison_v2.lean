-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
-- name    : AvramDividend.Classical.avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:38:57.595202+00:00
-- url     : https://prove2.me/theorems/f8c60858-ffcb-416a-bc01-1a43468afde5
-- title:
--   Factorised linear ODE supersolution upper bound
-- statement:
--   A C² supersolution to the factorised second-order equation has an exponential majorant with the positive characteristic root.
-- source:
--   A source-exact reduction of the scalar Gaussian-HJB ODE growth leaf; root algebra and analytic derivative comparison can be proved independently.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, w y ≤ K * Real.exp (rpos * y) := by sorry
