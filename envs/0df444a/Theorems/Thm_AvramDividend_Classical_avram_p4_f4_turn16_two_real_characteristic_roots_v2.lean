-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_two_real_characteristic_roots_v2
-- name    : AvramDividend.Classical.avram_p4_f4_turn16_two_real_characteristic_roots_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:38:53.259316+00:00
-- url     : https://prove2.me/theorems/16dae924-2f56-4e97-bac7-05d7cac74add
-- title:
--   Positive and negative real characteristic roots
-- statement:
--   The quadratic a r²+c r-q has one positive and one negative real root when a,q>0.
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

theorem AvramDividend.Classical.avram_p4_f4_turn16_two_real_characteristic_roots_v2
    (a c q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∃ rpos rneg : ℝ, 0 < rpos ∧ rneg < 0 ∧
      a * (rpos + rneg) = -c ∧ a * (rpos * rneg) = -q := by sorry
