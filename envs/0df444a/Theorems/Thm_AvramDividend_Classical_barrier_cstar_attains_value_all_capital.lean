-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
-- name    : AvramDividend.Classical.barrier_cstar_attains_value_all_capital
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:25:44.032976+00:00
-- url     : https://prove2.me/theorems/2a1720c5-cc96-431e-bf64-b5caff57cf80
-- title:
--   Barrier at finite c* is admissible under the cap and attains its scale-function value for every initial surplus
-- statement:
--   For the classical spectrally negative Levy dividend model, let W be its q-scale function and assume the optimal barrier c* is finite. The reflected barrier policy at c* is admissible with post-time-zero surplus bounded by c*. For every initial surplus x >= 0, including x > c* where the policy pays an initial excess lump sum, its expected discounted dividend value equals vcstar(W,x). This isolates the reflected-process admissibility and value identity underlying Theorem 2(i). It is a substantive stochastic-process obligation; proving it requires the reflection construction, barrier value formula, and the above-barrier initial payment boundary case.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 (pp.7-9) and Theorem 2(i) (pp.14-16).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_attains_value_all_capital {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
