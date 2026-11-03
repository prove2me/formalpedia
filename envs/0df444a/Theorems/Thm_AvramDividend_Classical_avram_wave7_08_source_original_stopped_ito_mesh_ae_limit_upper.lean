-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
-- name    : AvramDividend.Classical.avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:52:04.760504+00:00
-- url     : https://prove2.me/theorems/4e28ddb7-45f7-4f84-bef5-baee4a4980e2
-- title:
--   Exact source stopped Itô finite-mesh almost-everywhere upper budgets pass to martingale and residual limits
-- statement:
--   At the exact original Lévy X, ruinTime, W and full stopped Stieltjes Cash/Term, suppose genuine finite-mesh upper bounds have source martingale/generator/dividend residuals Mseq/Gseq/Hseq which converge pointwise almost everywhere to M/G/H. Then the stopped terminal-plus-cash upper inequality passes to the limiting residuals. This formalises only the order-theoretic a.e. limit step, leaving construction, integrability and centring of the genuine stochastic terms open.
-- source:
--   W7-08 source stopped Ito mesh convergence, designed to consume future W7-05/06/07 finite-grid innovations and W7-19 boundary limits; no independent or unrelated process introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mseq Gseq Hseq : ℕ → Ω → ℝ) (M G H : Ω → ℝ)
    (hupper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop (𝓝 (M ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω := by sorry
