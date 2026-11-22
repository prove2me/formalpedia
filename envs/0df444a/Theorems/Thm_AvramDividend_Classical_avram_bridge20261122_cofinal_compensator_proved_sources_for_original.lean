-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_cofinal_compensator_proved_sources_for_original
-- name    : AvramDividend.Classical.avram_bridge20261122_cofinal_compensator_proved_sources_for_original
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:47:10.244485+00:00
-- url     : https://prove2.me/theorems/f9bb5b25-6f8c-4702-9dd9-b0f267a7d58d
-- title:
--   Original UBV stopped Ito source with physically cofinal compact negative mark compensator controls
-- statement:
--   Original UBV stopped Ito source with physically cofinal compact negative mark compensator controls. The original physical stopped X,D,clock, dividend cash and terminal bound are retained. The additional assumptions are exact source-authentic proven interfaces on this same Levy process (or sample probability measure). The open child must apply these concrete mesh and terminal identities in an actual physical stopped stochastic-budget proof; no claim of the missing Ito or HJB expectation is introduced.
-- source:
--   Accepted root-connected physical Avram parent fdb9a6a3-8833-4d25-bb20-d197ce675232 and already-Proved export sources 241eab7e-b245-4060-a05a-4766abda9e9a, 2b3d8e28-d945-431b-ac32-1492923983c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_cofinal_compensator_proved_sources_for_original
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
    (hCofinalCompensatorSources : (∀ (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C),
let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0)
      (μ : Measure ((ℝ≥0 × Ω) × ℝ)),
      (∫ p, if
        (((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) ∧
          Y p.1.1 p.1.2 ∈ Icc (a n) (b n)) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ) =
      (∫ p, if
        ((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ)) ∧
      (∀ (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C),
let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0) (z : ℝ),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      Y t ω ∈ Icc c d → z < 0 →
      (if (((t : ℝ≥0∞) ≤
          min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
          Y t ω ∈ Icc (a n) (b n)) ∧ z < 0) then
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω))
      else 0) =
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω)))) :
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
