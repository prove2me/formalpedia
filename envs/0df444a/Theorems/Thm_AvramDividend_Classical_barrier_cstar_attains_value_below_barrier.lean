-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_below_barrier
-- name    : AvramDividend.Classical.barrier_cstar_attains_value_below_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T09:58:30.694774+00:00
-- url     : https://prove2.me/theorems/b36944c5-f5e0-4985-89ba-60298106c938
-- title:
--   The finite c* barrier is admissible and attains vcstar at and below the barrier
-- statement:
--   Let X satisfy the standing assumptions, q>0, W be its q-scale function, and assume the optimal barrier c* is finite. For every initial surplus 0<=x<=c*, the constant barrier strategy at c* is admissible in the capped class Pi_{<=c*}, and its expected discounted dividend value is exactly the candidate barrier value vc*(x). This is the below-barrier and boundary part of Proposition 1 specialised to c*, together with the pathwise reserve-cap property of reflection. It deliberately excludes x>c*, whose initial excess payment is handled by the already Proved add_initial_excess_admissible_value theorem.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 (pp. 7-9), equations (3.12)-(3.14), and Theorem 2(i) (pp. 14-16).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_attains_value_below_barrier {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
