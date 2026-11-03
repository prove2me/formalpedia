-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:46:49.701394+00:00
-- url     : https://prove2.me/theorems/3fa019a2-4792-4ae9-9b7f-6408ee3a45a5
-- title:
--   Real-valued sharp necessary allowance at the original BV zero-cap boundary
-- statement:
--   For the original Standing finite negative-jump activity bounded-variation Lévy dividend source at x=C=0 and q>0, any real W uniformly bounding each original finite-horizon expected complete stopped discounted Stieltjes payout must satisfy W≥drift/(q+ν((−∞,0)).toReal). The strict positivity of the ratio uses Proved nonmonotone BV positive drift 0432f641 and q>0; Proved exact ENNReal comparison fa374bd0 then transfers to real order using revision-pinned Mathlib ENNReal.ofReal_lt_ofReal_iff. The bound is sharp as a necessary infinite-horizon value threshold, and explicitly conditional on the existence of Standing finite-activity BV X.
-- source:
--   Canonical X, Ω, P, 𝓕, original barrier and complete Stieltjes payout; Proved fa374bd0 and 0432f641; Mathlib ENNReal order lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W := by sorry
