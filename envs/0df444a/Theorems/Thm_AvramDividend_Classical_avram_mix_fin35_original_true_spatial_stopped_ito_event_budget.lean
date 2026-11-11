-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin35_original_true_spatial_stopped_ito_event_budget
-- name    : AvramDividend.Classical.avram_mix_fin35_original_true_spatial_stopped_ito_event_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T23:21:52.514269+00:00
-- url     : https://prove2.me/theorems/1a3d64f9-b225-4a2f-9802-5b1e46d91ff0
-- title:
--   Original finite-mixed Itô event budget on genuine compact upper-exit stopped clocks
-- statement:
--   For the original spectrally negative Lévy path, its actual adapted dividend strategy, finite negative-jump activity, finite dividend cap and every bounded ruin-clipped stopping clock, prove the expected discounted closed physical dividend cash plus correct postpayment-or-ruin terminal reward is at most the initial HJB value times the initial event mass on every true spatially localised upper-passage clock. Every localised clock is the exact minimum of the original clock and the genuine upper exit at level k+1. The proof must establish a single original-filtration stopped Gaussian and compensated negative-jump Itô–Stieltjes ledger including initial dividends, pre-ruin payments, terminal and ruin atoms. Use compact source-noise integrability; do not assume a globally integrable raw jump size.
-- source:
--   Source-faithful compact physical Itô core for original Open 04aca600 and 52a16569. Already Proved cfcb0f9d constructs the exact cofinal clocks, 4f61f549 establishes local reward measurability and L1, ff307c5e transfers the compact budgets by exact cofinal Fatou. This child isolates the remaining stochastic Itô inequality on the original X,D and original filtration; it does not assume an auxiliary independent Brownian process or unjustified first absolute negative-jump moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin35_original_true_spatial_stopped_ito_event_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ k, (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, H k ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | ρ η ≠ 0})).toReal := by sorry
