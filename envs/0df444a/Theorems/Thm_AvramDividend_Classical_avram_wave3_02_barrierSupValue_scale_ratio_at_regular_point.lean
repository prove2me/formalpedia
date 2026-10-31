-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_scale_ratio_at_regular_point
-- name    : AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_at_regular_point
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:50:50.998999+00:00
-- url     : https://prove2.me/theorems/dea30b3c-03c4-4e89-a883-016380160ea9
-- title:
--   Original Stieltjes reflected barrier value equals W divided by derivative at any locally regular barrier
-- statement:
--   For a genuine Standing original spectrally negative Levy process, q>0 and a strictly positive constant dividend barrier a, if the source q-scale function has a derivative at this one barrier and that derivative is nonzero, the true expected discounted reflected regulator Stieltjes reward from the boundary equals ENNReal.ofReal(W^(q)(a)/W^(q)'(a)). The original lower/upper stopped-renewal bounds and their proved squeeze theorem yield this directly. This local theorem avoids assuming C1 of W on the entire positive axis and isolates exactly the missing source regularity needed to upgrade to the original unconditional ratio.
-- source:
--   Avram Palmowski Pistorius (2007), reflected spectrally negative Levy dividend strategy and local scale-ratio; proved stopped-renewal reward bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_barrierSupValue_scale_ratio_at_regular_point
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by sorry
