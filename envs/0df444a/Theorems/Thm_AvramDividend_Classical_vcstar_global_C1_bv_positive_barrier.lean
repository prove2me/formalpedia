-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
-- name    : AvramDividend.Classical.vcstar_global_C1_bv_positive_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:16:37.213038+00:00
-- url     : https://prove2.me/theorems/8837ab3a-7d73-4496-8c77-29bfe0c2d749
-- title:
--   BV regularity: globally C1 positive optimal dividend barrier across its join
-- statement:
--   Bounded-variation positive-barrier case of the global verification regularity theorem. Under Standing condition (3.3), the scale function is C1 on (0,∞); below c* the barrier candidate is W/W'(c*), above c* it is affine, and smooth fit at the derivative-minimising c* joins them with matching first derivative one. Prove global C1 regularity across c* as required for applying the stochastic verification proposition with C=∞. The open proof requires genuine scale-function regularity and derivative-minimiser analysis, not just piecewise continuity.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), Proposition 3(i) and Theorem 2, smooth fit for the BV barrier candidate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_global_C1_bv_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
  sorry
end AvramDividend.Classical
