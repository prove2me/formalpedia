-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_finitecap_preruin_physical_budget
-- name    : AvramDividend.Classical.avram_bv_correct12_original_finitecap_preruin_physical_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:31:36.205122+00:00
-- url     : https://prove2.me/theorems/f053f7c1-fe70-4b10-b4e3-31d85796e2b5
-- title:
--   Original BV finite-cap physical dividend budget on all admissible pre-ruin prefixes
-- statement:
--   A direct original-process consequence of finite-cap admissibility, pre-ruin postpayment solvency and the public closed-cap physical dividend estimate. The same pathwise constant L works for all pairs of times up to any deterministic pre-ruin clock, with reserves automatically inside the closed cap. It does not assert the discounted expectation inequality.
-- source:
--   Original finite-activity BV source 8271cf4d and finite-cap parent 3993433e. Instantiates public Proved 3eadd48e with 16104f4f and f23e585c to remove its otherwise external reserve-band hypotheses on true admissible pre-ruin paths.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_original_finitecap_preruin_physical_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, (T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) →
        ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
          (rightLimit D t ω - rightLimit D s ω) +
            (w (x + X.X t ω - rightLimit D t ω) -
              w (x + X.X s ω - rightLimit D s ω)) ≤
            L * (((t : ℝ) - (s : ℝ)) * X.drift) := by sorry
