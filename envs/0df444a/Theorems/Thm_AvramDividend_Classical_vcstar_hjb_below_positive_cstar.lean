-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
-- name    : AvramDividend.Classical.vcstar_hjb_below_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:30:50.582748+00:00
-- url     : https://prove2.me/theorems/93145b5a-25dd-4cc0-9e9a-04d2275120f7
-- title:
--   The c* barrier candidate satisfies the HJB equation below a positive finite barrier
-- statement:
--   Assume c* is positive and finite. On every capital y strictly between 0 and c*, Lemma 4 gives (Gamma-q)vc*=0 and generator integrability, while Lemma 3 gives vc*'(y)>=1. Hence both entries of max{Gamma vc*-q vc*, 1-vc*'} are nonpositive and the first is exactly zero, so the HJB maximum is zero. The smoothness disjunction of Theorem 2 is restricted from (0,infinity) to (0,c*) when needed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 3(i), Lemma 4, equation (5.8), and proof of Theorem 2, pp. 16-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_hjb_below_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcfin : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry

end AvramDividend.Classical
