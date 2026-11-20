-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_trueclock_Ito_physical_signed_remainder_vanish
-- name    : AvramDividend.Classical.avram_jump6_A_original_trueclock_Ito_physical_signed_remainder_vanish
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:41:00.515179+00:00
-- url     : https://prove2.me/theorems/ba308fc4-cce1-41ea-b01d-4263704bf5de
-- title:
--   Original ruin-clipped physical mixed Ito remainder vanishes for genuine intrinsic two-channel gains
-- statement:
--   Prove the actual stopped mixed Gaussian/negative-mark Itô-Meyer source: once the intrinsic Gaussian and full compensated jump noise processes are fixed as their Lévy-process limits, the exact ruin-clipped discounted postpayment cash and Iic dividend reward is bounded by initial w(x) plus these noise gains and integrable finite-grid remainders whose signed eventwise expectations tend nonpositive. This is the physical source still missing after signed HJB and martingale centring are proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_trueclock_Ito_physical_signed_remainder_vanish
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
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
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
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
    ∀ (k : ℕ) (A : Set Ω),
      MeasurableSet[𝓕.rightCont 0] A →
      ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto (fun j : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
            atTop (nhds (R t ω))) →
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto (fun j : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
            atTop (nhds (Jsmall t ω))) →
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Jfull t ω = Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
            (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
        ∃ (Err : ℕ → Ω → ℝ),
          (∀ m, IntegrableOn (Err m)
            (A ∩ {η : Ω | κ k η ≠ 0}) P) ∧
          (∀ m, ∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})),
            H k ω ≤ w x + (R (κ k ω) ω + Jfull (κ k ω) ω) +
              Err m ω) ∧
          (∀ ε : ℝ, 0 < ε →
            ∃ m, (∫ ω in A ∩ {η : Ω | κ k η ≠ 0},
              Err m ω ∂P) ≤ ε) := by sorry
