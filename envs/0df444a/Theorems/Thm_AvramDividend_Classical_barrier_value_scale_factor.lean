-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor
-- name    : AvramDividend.Classical.barrier_value_scale_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T08:26:24.359917+00:00
-- url     : https://prove2.me/theorems/e185eb4b-39be-442d-b6f8-61627a0f122d
-- title:
--   Strong-Markov scale factor: V(x) = (W(x)/W(a)) * V(a) with W(a) > 0
-- statement:
--   Strong-Markov scale factor for the barrier strategy (Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, p. 8, proof of Proposition 1). Let X be a spectrally negative Levy process satisfying the standing assumptions, q > 0, W its q-scale function, a > 0 and 0 <= x <= a. Then W(a) > 0, and the expected discounted dividends of the barrier strategy started from x factor as V(x) = (W(x)/W(a)) * V(a), where V(a) is the boundary value at the barrier. The paper obtains this by applying the strong Markov property of the reflected process Y at tau-hat^0 = inf{t >= 0 : Y_t = 0}, so that {Y_t, t <= tau-hat^0} is in law equal to {-X_t, t <= T^+_0} started at x - a, and closing the resulting prefactor E_{x-a}[e^{-q tau-hat^0} 1{tau-hat^0 < tau-hat^a}] with the two-sided exit identity (3.6), E_x[e^{-q T^+_a}] = W(x)/W(a), using W(y) = 0 for y <= 0. Combined with the boundary identity V(a) = W(a)/W'(a) (eq. 3.13, the sibling theorem barrier_value_eq_scale_ratio_at_barrier), this yields Proposition 1 for general x. This child isolates exactly the x-dependent analytic input; the remaining algebra combining the two factors is elementary.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, p. 8, proof of Proposition 1 (strong-Markov step at tau-hat^0 and two-sided exit identity (3.6))

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem barrier_value_scale_factor {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by sorry

end AvramDividend.Classical
