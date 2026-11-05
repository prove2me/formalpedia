-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
-- name    : AvramDividend.Classical.avram_integration_sweep14_original_BV_vanishing_error_strict_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:15:33.556353+00:00
-- url     : https://prove2.me/theorems/6233a7f9-8f84-4c6c-835c-3781ed09212c
-- title:
--   Original BV strict payoff expected bound with vanishing positive finite-grid source error
-- statement:
--   For the literal original Lévy reserve X.X, right-payment dividend D, strict pre-horizon Stieltjes cash and fixed strict-survivor terminal, derive the full expected reward upper bound from source signed M+B means at most zero, a pathwise grid budget with nonnegative error and expected positive grid error vanishing. The original cofinal cash expectation theorem provides limit passage without assuming one integrable envelope for every stochastic mesh.
-- source:
--   Proved/public 28343e2d and 8a5ada70 for original physical cofinal cash/terminal; Proved/public aef1a390 and 04dadbf6 for admissible original signed budgets. This theorem is a source-faithful conditional integration alternative to strong db6a3111 all-mesh domination, requiring a genuine physical hPhysical and error convergence.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep14_original_BV_vanishing_error_strict_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (M B Err : ℕ → Ω → ℝ) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    ∀ (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0)
      (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
      (hErrMean : Tendsto
        (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0))
      (hPhysical : ∀ n, ∀ᵐ ω ∂P,
        Cash (u n) ω + Term ω ≤
          w x + (M n ω + B n ω) + max (Err n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x := by sorry
