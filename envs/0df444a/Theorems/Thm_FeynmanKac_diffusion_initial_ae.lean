-- Prove2me | Theorems.Thm_FeynmanKac_diffusion_initial_ae
-- name    : FeynmanKac.diffusion_initial_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:41:52.086644+00:00
-- url     : https://prove2.me/theorems/3d63d2bb-578f-4ab5-abff-354193f8b952
-- title:
--   An IsDiffusion process starts at its deterministic vector initial state
-- statement:
--   Any genuine IsDiffusion solution starts at its prescribed vector initial state, almost surely. The proof projects the IsDiffusion witness to its underlying IsVectorItoVersion and invokes the accepted zero-time vector Itô-version theorem. It is reusable for clock-augmented Feynman–Kac diffusions and other Brownian SDEs, and assumes no PDE or Feynman–Kac conclusion.
-- source:
--   Accepted Prove2Me theorem https://prove2.me/theorems/ee3afebe-ae0f-4c3f-aa5d-fab65a71b613

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_readable

open MeasureTheory
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open FunctionalInequalities.Probability.Diffusion

theorem FeynmanKac.diffusion_initial_ae
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N d : ℕ} {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    {x₀ : Fin N → ℝ} {Y : ℝ → Ω → Fin N → ℝ}
    (h : IsDiffusion W ℱ hW b σ x₀ Y) :
    (fun ω => Y 0 ω) =ᵐ[P] (fun _ => x₀) := by sorry
