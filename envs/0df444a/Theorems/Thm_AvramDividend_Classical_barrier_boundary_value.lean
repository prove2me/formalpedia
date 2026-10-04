-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_boundary_value
-- name    : AvramDividend.Classical.barrier_boundary_value
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T08:49:36.98209+00:00
-- url     : https://prove2.me/theorems/0443131f-ee5d-4b85-9285-8841e2116e92
-- title:
--   Boundary value at the barrier: V(a) = W(a)/W'(a) (clean preamble)
-- statement:
--   Boundary value of the barrier strategy at the barrier (Avram, Palmowski, Pistorius, arXiv:math/0702893v1, p. 8, eq. (3.13), via Theorem 1 of Avram-Kyprianou-Pistorius 2004). Let X be a spectrally negative Levy process satisfying the standing assumptions, q > 0, W its q-scale function and a > 0. Then the expected discounted dividends of the constant barrier strategy started at the barrier equal W(a)/W'(a): E_0[integral_0^{tau-hat^a} e^{-qt} dS_t] = W(a)/W'(a), where tau-hat^a = inf{t : S_t - X_t > a} is the drawdown ruin time. This is the x = a instance of Proposition 1 and needs no translation of the law. It is stated here with a minimal preamble over the three core definition modules only, so that proof sketches can import it without depending on the deprecated AvramDividend_Classical_ReflectionCapital module pinned by the sibling statement barrier_value_eq_scale_ratio_at_barrier.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, p. 8, eq. (3.13), via Theorem 1 of Avram-Kyprianou-Pistorius (2004)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem barrier_boundary_value {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) := by sorry

end AvramDividend.Classical
