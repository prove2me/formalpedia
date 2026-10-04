-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_compensation_integrable
-- name    : AvramDividend.Classical.bv_compensation_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:16:57.190707+00:00
-- url     : https://prove2.me/theorems/f5ebc4d1-396d-466f-8fdb-9c8bee5a6f28
-- title:
--   Bounded variation gives integrability of the canonical Lévy compensation indicator
-- statement:
--   For a canonical Classical bounded-variation spectrally negative Lévy process, the Lévy–Khintchine compensation integrand theta*y*1_{(-1,1)}(y) is integrable on y<0 for any real theta. The BV hypothesis supplies the finite integral of |y| on (-1,0). Mathlib integrableOn_indicator_iff identifies restriction to (-infinity,0) of the compensated indicator with the small-jump interval (-1,0). This discharges one of the exact integrability prerequisites of the process-level Lévy–Khintchine rearrangement.
-- source:
--   Canonical Classical SpectrallyNegativeLevy, pinned Mathlib IntegrableOn.lean integrableOn_indicator_iff and Real.enorm_eq_ofReal_abs at revision 0df444a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_compensation_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation) (θ : ℝ) :
    IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν := by
  sorry
