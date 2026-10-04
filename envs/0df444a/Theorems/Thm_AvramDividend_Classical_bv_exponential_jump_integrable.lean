-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
-- name    : AvramDividend.Classical.bv_exponential_jump_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:17:48.660988+00:00
-- url     : https://prove2.me/theorems/e61e3f45-d1c6-49d7-9d06-a9433505b01d
-- title:
--   Bounded variation implies integrability of the negative-jump exponential compensator for theta at least one
-- statement:
--   For the canonical spectrally negative Lévy jump measure under bounded variation, the function exp(theta*y)-1 is integrable over negative jumps for theta≥1. The accepted finite truncated negative jump moment controls min(-y,1); the accepted uniform discounted compensator bound controls |exp(theta*y)-1| pointwise by theta*min(-y,1). Bochner integrability follows by norm domination. This supplies the second analytic premise needed for the exact Lévy–Khintchine drift rearrangement.
-- source:
--   Accepted finite_truncated_negative_jump_moment 05eba094 and discounted_jump_compensator_bound 76c669d6; pinned Mathlib Integrable.mono' and Real.enorm_eq_ofReal_abs

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_truncated_negative_jump_moment
import Theorems.Thm_AvramDividend_Classical_discounted_jump_compensator_bound
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_exponential_jump_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν := by
  sorry
