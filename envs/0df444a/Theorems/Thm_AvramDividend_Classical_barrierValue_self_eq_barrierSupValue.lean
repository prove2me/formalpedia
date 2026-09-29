-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
-- name    : AvramDividend.Classical.barrierValue_self_eq_barrierSupValue
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T08:37:39.620406+00:00
-- url     : https://prove2.me/theorems/11b589b7-37f0-4756-acd5-e1ea2d41f67a
-- title:
--   At the boundary x = a the constant barrier strategy equals the running supremum, so its value is the barrier supremum value
-- statement:
--   At the boundary `x = a` the constant barrier strategy started from capital `a` is exactly the
--   reflection at the running supremum, `barrierStrategy X a a = runningSup X`, so its ruin time is
--   the barrier ruin time `tau-hat^a = inf{t >= 0 : S_t - X_t > a}`, and the two discounted dividend
--   values coincide.
--
--   This is the deterministic half of Proposition 1, eq. (3.12), of Avram, Palmowski and Pistorius,
--   arXiv:math/0702893v1, p. 8, restricted to the boundary `x = a`. It is exactly the left-hand
--   equality of that display,
--
--     dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q,
--
--   with no fluctuation theory involved: the claim is a definitional unfolding once the controlled risk
--   process `U^a_t = a + X_t - S_t = a - (S_t - X_t)` is read as `a` minus the drawdown.
--
--   The paper supplies the justification in §3.3 (p. 7) and p. 12: the controlled process started from
--   `x` with barrier `a` has the same law as `a - Y+` started from `a - x`, so at `x = a` the ruin
--   condition `U^a_t < 0` is `S_t - X_t > a`, which is the definition of `barrierRuinTime`.
--
--   **Formalization Note.** Both values are taken in `[0, infinity]` under the single base measure `P`.
--   No translated law is involved: at `x = a` the translate `x - a` vanishes, which is why this
--   boundary case needs no measure change. The stochastic content of eq. (3.12) is the separate
--   identity `barrierSupValue X a q = W(a)/W'(a)`; this child isolates only the deterministic bridge.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 eq. (3.12) on p. 8 at the boundary x = a; same-law identification in section 3.3 (p. 7) and p. 12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem barrierValue_self_eq_barrierSupValue {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (a : ℝ) :
    dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q := by sorry

end AvramDividend.Classical
