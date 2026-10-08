-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le_unbounded_variation
-- name    : AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:12:03.666991+00:00
-- url     : https://prove2.me/theorems/132447c8-f5f2-4688-8ccd-ef2cbc009efd
-- title:
--   Local verification for one capped strategy in the unbounded-variation case
-- statement:
--   Unbounded-variation branch of Proposition 4(i) for one capped admissible dividend strategy. With w C² on the positive capped reserve domain, apply the stopped Itô formula to exp(-qt)w(Ut), use Γw−qw≤0 and w′≥1 from (5.8), control dividend jumps, localise the martingale, and pass to the full dividend integral.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, C² Itô/localisation branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
