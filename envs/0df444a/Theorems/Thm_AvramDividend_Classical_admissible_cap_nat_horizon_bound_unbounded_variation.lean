-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_nat_horizon_bound_unbounded_variation
-- name    : AvramDividend.Classical.admissible_cap_nat_horizon_bound_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:26:04.422652+00:00
-- url     : https://prove2.me/theorems/61bbf167-9a2e-4827-9545-df3d5df758e9
-- title:
--   Finite-horizon verification inequality in the unbounded-variation case
-- statement:
--   Under the unbounded-variation branch of Proposition 4(i), every capped admissible policy satisfies the verification dividend bound at each deterministic integer horizon. This is the finite-horizon form obtained by stopped C² Itô localisation before the final monotone-convergence passage.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, stopped Itô/localisation argument leading to (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_nat_horizon_bound_unbounded_variation
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
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
