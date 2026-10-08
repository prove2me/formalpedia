-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
-- name    : AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:42:56.927707+00:00
-- url     : https://prove2.me/theorems/edf21020-2dbd-48f9-82ea-adf0f40c61d9
-- title:
--   Smooth fit gives derivative one at a positive optimal barrier
-- statement:
--   For positive finite c*, the candidate barrier value is differentiable at c* and its right-side affine branch has slope one. Smooth fit therefore gives the derivative exactly one at the join. This strengthens the derivative-at-least-one milestone only at the barrier, supplying the vanishing marginal-dividend term for the HJB endpoint.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale-derivative minimiser (5.2), smooth fit in Proposition 3(i) and Theorem 2, pp. 14-16.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_deriv_eq_one_at_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  sorry
end AvramDividend.Classical
