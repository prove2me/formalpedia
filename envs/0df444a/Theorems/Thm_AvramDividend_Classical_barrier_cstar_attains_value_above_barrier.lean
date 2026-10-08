-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_above_barrier
-- name    : AvramDividend.Classical.barrier_cstar_attains_value_above_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T11:31:55.031029+00:00
-- url     : https://prove2.me/theorems/a14f4b34-5c06-49bd-8571-4928130c258d
-- title:
--   Above finite c*, the barrier policy pays the initial excess and attains vcstar
-- statement:
--   Let c* be finite. For initial surplus x>c*, the constant barrier strategy pays the deterministic excess x-c* at time zero and then follows the barrier strategy started from c*. It remains admissible in Pi_{<=c*}, and its total expected discounted dividend value equals the affine branch vc*(x)=x-c*+vc*(c*). This is the above-barrier initial-payment extension of Proposition 1 and Theorem 2(i). The formal proof should use the already Proved barrierStrategy_eq_add_initial_excess_above_barrier and add_initial_excess_admissible_value results together with the c* boundary value and the nonnegativity needed for the ENNReal ofReal sum.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Section 3.3 (barrier strategy), Proposition 1 (pp. 7-9), equation (5.1), and Theorem 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_attains_value_above_barrier {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, (cstar W).toReal < x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
