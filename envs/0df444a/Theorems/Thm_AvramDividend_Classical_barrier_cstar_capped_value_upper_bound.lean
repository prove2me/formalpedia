-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound
-- name    : AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:11:36.649557+00:00
-- url     : https://prove2.me/theorems/b53cddad-64e6-4a89-92bf-50c9a4f5f41d
-- title:
--   Verification upper bound for the capped dividend problem at the finite optimal barrier
-- statement:
--   Under the standing assumptions, q>0, the scale-function identity, finiteness of c*, and the smoothness condition of Theorem 2, the candidate barrier value vc* is an upper bound for the value of every admissible strategy whose controlled surplus is capped by c*. Equivalently, for every x>=0, the capped value function valueFunctionLe X q c* x is at most vc*(x). This is exactly the verification inequality needed for Theorem 2(i), separated from the independent fact that the barrier strategy attains the bound.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 3(i), Proposition 4(i), and Theorem 2(i), pp. 15-20.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_capped_value_upper_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
