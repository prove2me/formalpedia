-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
-- name    : AvramDividend.Classical.avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:50:54.80527+00:00
-- url     : https://prove2.me/theorems/5ff1403b-ab62-4841-9a0f-b4140c636391
-- title:
--   True reflected barrier ratio from a nonzero local scale derivative
-- statement:
--   For a positive barrier and a genuine q-scale function under Standing, a nonzero ordinary scale derivative at that barrier suffices to evaluate the actual killed reflected-supremum Stieltjes dividend value by W(a)/W'(a). No global positive-axis differentiability is assumed.
-- source:
--   Avram–Palmowski–Pistorius 2007 Proposition 1, canonical Proved stopped-renewal lower and upper bounds 6b821aa5 and c6c3b1d0, Proved hasDerivAt_of_deriv_ne_zero 23ad363d, and exact converter 3c69ef7b. Enables a local cstar route under the root's C2(vcstar) alternative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hNe : deriv W a ≠ 0) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by sorry
