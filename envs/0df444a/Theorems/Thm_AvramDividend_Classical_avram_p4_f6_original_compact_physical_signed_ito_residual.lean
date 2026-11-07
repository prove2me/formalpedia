-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_compact_physical_signed_ito_residual
-- name    : AvramDividend.Classical.avram_p4_f6_original_compact_physical_signed_ito_residual
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:28:18.261937+00:00
-- url     : https://prove2.me/theorems/736ff879-c858-4cdb-944b-c8afdc791ea7
-- title:
--   Original compact stopped Ito physical signed residual is integrable with nonpositive expectation
-- statement:
--   For one genuinely cap-compatible cofinal sequence of stopping times of the original Lévy dividend source, construct the actual stopped discounted reward F_k and an integrable signed Itô–Meyer residual M_k on the same sample space. The physical compensator/decomposition should give F_k≤w(x)+M_k almost everywhere and E[M_k]≤0. Also establish L1 and positivity of each actual stopped F_k. This is the true probabilistic source reduction; the existing generic signed residual expectation theorem then yields the finite-clock mean budget without assuming natural-clock martingale uniform integrability.
-- source:
--   Physical one-cell original stopped Gaussian, small/large compensated jumps, generator drift and dividend/ruin/cap residual combined as M_k. May reuse accepted original L2 finite-grid martingales, but still requires genuine original Ito–Meyer identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f6_original_compact_physical_signed_ito_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (F M : ℕ → Ω → ℝ),
      0 ≤ w x ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Measurable (F k)) ∧
      (∀ k, Integrable (F k) P) ∧
      (∀ k, 0 ≤ᵐ[P] F k) ∧
      (∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, σ k ω = τ ω) ∧
      (∀ k, Integrable (M k) P) ∧
      (∀ k, (∫ ω, M k ω ∂P) ≤ 0) ∧
      (∀ k, ∀ᵐ ω ∂P, F k ω ≤ w x + M k ω) := by sorry
