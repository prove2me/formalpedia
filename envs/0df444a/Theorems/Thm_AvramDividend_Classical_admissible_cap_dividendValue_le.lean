-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le
-- name    : AvramDividend.Classical.admissible_cap_dividendValue_le
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:05:47.464087+00:00
-- url     : https://prove2.me/theorems/297e63cd-feca-4383-a09c-1df906ae8ff1
-- title:
--   Itô–localisation bound for one dividend strategy constrained below C
-- statement:
--   Under precisely the hypotheses of Proposition 4(i), any single admissible dividend strategy whose controlled reserve is capped at C has expected discounted dividends up to ruin no greater than ENNReal.ofReal (w x), for 0 ≤ x and ENNReal.ofReal x ≤ C. This isolates the substantive controlled-jump Itô, localisation, discounted martingale, finite-variation payout and stopping argument. A separate lattice-supremum argument yields Proposition 4(i).
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), p. 18, proof from (5.8) via Itô's formula for the stopped surplus process; source-faithful single-policy reduction of theorem AvramDividend.Classical.local_verification (f318a688-56f8-459d-865b-f64d192f9630).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_dividendValue_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
