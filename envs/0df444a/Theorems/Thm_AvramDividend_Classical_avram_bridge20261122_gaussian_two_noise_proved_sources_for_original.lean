-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_gaussian_two_noise_proved_sources_for_original
-- name    : AvramDividend.Classical.avram_bridge20261122_gaussian_two_noise_proved_sources_for_original
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:54:36.639949+00:00
-- url     : https://prove2.me/theorems/371e4497-273f-4017-ba7e-94a342fcd261
-- title:
--   Original UBV stopped Ito source with proved Gaussian and second-order two-channel L2 mesh-energy convergence
-- statement:
--   Original UBV stopped Ito source with proved Gaussian and second-order two-channel L2 mesh-energy convergence. The original physical stopped X,D,clock, dividend cash and terminal bound are retained. The additional assumptions are exact source-authentic proven interfaces on this same Levy process (or sample probability measure). The open child must apply these concrete mesh and terminal identities in an actual physical stopped stochastic-budget proof; no claim of the missing Ito or HJB expectation is introduced.
-- source:
--   Accepted root-connected physical Avram parent fdb9a6a3-8833-4d25-bb20-d197ce675232 and already-Proved export sources 85b94339-1b0f-4212-813f-35206e681a29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
open Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bridge20261122_gaussian_two_noise_proved_sources_for_original
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
    (hCashI : Integrable Cash P)
    (hGaussianTwoNoiseSources : (∀ (L Q : ℕ → Ω → ℝ) (K : ℕ × ℕ → ℝ)
    (σ C : ℝ) (hC : 0 ≤ C)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P)
    (hLISO : ∀ m l,
      (∫ ω, (L m ω - L l ω) ^ 2 ∂P) = σ ^ 2 * K (m, l))
    (hK : Tendsto K atTop (𝓝 (0 : ℝ)))
    (hQNonneg : ∀ m, 0 ≤ ∫ ω, (Q m ω) ^ 2 ∂P)
    (hQRate : ∀ m,
      (∫ ω, (Q m ω) ^ 2 ∂P) ≤ C / ((m + 1 : ℕ) : ℝ)),
Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)))) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
