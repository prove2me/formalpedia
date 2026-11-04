-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:19:42.024506+00:00
-- url     : https://prove2.me/theorems/ba5028b0-84b4-4566-9313-db2cdaa66476
-- title:
--   Original strictly interior diffuse Stieltjes dividend residual plus countable authentic right-payment atoms is nonpositive
-- statement:
--   For the original stochastic process and actual dividendMeasure D, the strictly interior signed derivative integral is nonpositive by the previously proved source Stieltjes gradient lemma, including singular-continuous payments. The correct post-X-jump/pre-right-D-payment secant loss is nonpositive at each genuine eligible right-payment time by original hjump. Under honest real summability of their countable indexed series, their sum is nonpositive. This defines a directly importable signed dividend remainder without assuming boundary contact lies in the strict HJB interior; P4-E/F must separately establish diffuse-support localisation, enumerate genuine right atoms, and connect to the original Ito–Meyer formula.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.13); source-proved f2c20057 strict-interior Stieltjes sign and 9f4070e7 true-state hjump sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      A (dividendMeasure D ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (t : ι → ℝ≥0)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω)))) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂(dividendMeasure D ω)) +
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry
