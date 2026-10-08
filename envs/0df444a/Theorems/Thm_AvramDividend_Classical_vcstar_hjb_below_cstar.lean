-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
-- name    : AvramDividend.Classical.vcstar_hjb_below_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:03:19.137811+00:00
-- url     : https://prove2.me/theorems/40aa4963-36df-4c37-9d31-1a99d28551ac
-- title:
--   HJB identity for the c-star candidate strictly below a positive finite barrier
-- statement:
--   For a positive finite optimal barrier c*, the candidate v_{c*} satisfies the classical HJB maximum equation at every point strictly between 0 and c*. The generator term is zero by Lemma 4, while Lemma 3(i) gives v'_{c*} >= 1, so the marginal-dividend term is nonpositive. This packages exactly the pointwise HJB hypothesis required by Proposition 4(i) below the barrier.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 3(i), Lemma 4 and equation (5.8), pp. 15-20. Source-faithful HJB assembly bridge for Theorem 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_hjb_below_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  sorry

end AvramDividend.Classical
