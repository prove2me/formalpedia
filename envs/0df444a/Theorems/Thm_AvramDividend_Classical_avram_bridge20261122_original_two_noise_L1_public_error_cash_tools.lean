-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_two_noise_L1_public_error_cash_tools
-- name    : AvramDividend.Classical.avram_bridge20261122_original_two_noise_L1_public_error_cash_tools
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:03:14.048143+00:00
-- url     : https://prove2.me/theorems/18984437-2e5f-43c5-a089-61d5f38a243c
-- title:
--   Original stopped Ito source with four public physical-event L1 bounds and vanishing-error lemmas
-- statement:
--   Retains the same original law P, surplus X,D, clipped clock, dividend cash and terminal. Four public Proved eventwise L1 budget and domination tools are imported. Fifth private B32 physical obstruction is excluded, and the child still needs true physical stopped stochastic centring.
-- source:
--   Original open fdb9a6a3, public heads 213ae04a,3d397c26,481be95a,c62669ff. Private head 6ff7dd41 explicitly omitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
open Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bridge20261122_original_two_noise_L1_public_error_cash_tools
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
    (hPublicL1Tools : (∀ (A : Set Ω) (hA : MeasurableSet A)
    (F W : Ω → ℝ) (G E : ℕ → Ω → ℝ)
    (hFI : Integrable F (P.restrict A))
    (hWI : Integrable W (P.restrict A))
    (hGI : ∀ n, Integrable (G n) (P.restrict A))
    (hEI : ∀ n, Integrable (E n) P)
    (hGmean : ∀ n, (∫ ω, G n ω ∂(P.restrict A)) = 0)
    (hEglobal : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂P) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ W ω + G n ω + E n ω),
(∫ ω, F ω ∂(P.restrict A)) ≤
      (∫ ω, W ω ∂(P.restrict A))) ∧
      (∀ (μ ν : Measure Ω) (hμν : μ ≤ ν)
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ n, Integrable (E n) ν)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂ν) atTop (𝓝 (0 : ℝ))),
Tendsto (fun n => ∫ ω, ‖E n ω‖ ∂μ)
      atTop (𝓝 (0 : ℝ))) ∧
      (∀ (A : Set Ω) (hA : MeasurableSet A)
    (F W : Ω → ℝ) (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F (P.restrict A))
    (hWI : Integrable W (P.restrict A))
    (hGI : ∀ n, Integrable (G n) (P.restrict A))
    (hJI : ∀ n, Integrable (J n) (P.restrict A))
    (hEI : ∀ n, Integrable (E n) P)
    (hGmean : ∀ n, (∫ ω in A, G n ω ∂P) = 0)
    (hJmean : ∀ n, (∫ ω in A, J n ω ∂P) = 0)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂P) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ W ω + G n ω + J n ω + E n ω)
    (δ : ℝ) (hδ : 0 < δ)
    (hGap : (∫ ω in A, W ω ∂P) + δ ≤
      (∫ ω in A, F ω ∂P)),
False) ∧
      (∀ (μ : Measure Ω) (Y B : Ω → ℝ)
    (M E : ℕ → Ω → ℝ)
    (hY : Integrable Y μ) (hB : Integrable B μ)
    (hM : ∀ n, Integrable (M n) μ)
    (hE : ∀ n, Integrable (E n) μ)
    (hMmean : ∀ n, (∫ ω, M n ω ∂μ) = 0)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂μ) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂μ,
      Y ω ≤ B ω + M n ω + E n ω),
(∫ ω, Y ω ∂μ) ≤ (∫ ω, B ω ∂μ))) :
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
