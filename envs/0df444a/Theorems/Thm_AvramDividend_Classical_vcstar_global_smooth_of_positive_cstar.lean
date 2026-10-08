-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_global_smooth_of_positive_cstar
-- name    : AvramDividend.Classical.vcstar_global_smooth_of_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:14:22.740847+00:00
-- url     : https://prove2.me/theorems/710416d9-ea5e-4de0-8e06-e250674de443
-- title:
--   Global C2 or C1 smoothness of the positive optimal barrier candidate, including its join
-- statement:
--   For a positive finite c*, establish the global piecewise regularity needed to apply Proposition 4(i) with C=∞, beyond the existing smoothness lemma limited to (0,c*). Below the barrier the candidate is W(x)/W'(c*) and inherits the scale function regularity, above it the candidate is affine. At their junction x=c*, smooth fit gives equality of first derivatives and in the Gaussian/C2 case the minimality of W'(c*) gives W''(c*)=0, matching the affine second derivative. Under the explicit C2 disjunct the conclusion is immediate. This is a substantive gluing theorem at the barrier and does not follow from a decorative graph link.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2 smoothness proviso, Lemma 3(i), Proposition 4(i), scale-function regularity (3.3); gluing the two branches of (5.1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_global_smooth_of_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
    (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0)) := by
  sorry
end AvramDividend.Classical
