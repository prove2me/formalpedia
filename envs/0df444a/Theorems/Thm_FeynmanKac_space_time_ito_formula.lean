-- Prove2me | Theorems.Thm_FeynmanKac_space_time_ito_formula
-- name    : FeynmanKac.space_time_ito_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:36:24.788595+00:00
-- url     : https://prove2.me/theorems/da1add00-8814-496b-9b82-eed59d60b931
-- title:
--   Time-dependent Itô formula for a real bounded diffusion
-- statement:
--   For a genuine clock-augmented Brownian diffusion X_s, a C¹ in time and C² in space function u, and its actual spatial-gradient Brownian integrand H(ω,r)=1_[0,T−t](r) σ(X_{t+r},t+r) ∂ₓu(X_{t+r},t+r), assume only the required measurable, progressively measurable and finite L² witnesses. Derive the time-dependent Itô formula on [t,s] with Brownian integral up to elapsed time s−t, using the independently established diffusion SDE and vector Itô formula. H is explicitly constrained to equal the true gradient coefficient; no martingale or Feynman–Kac representation identity is assumed.
-- source:
--   Feynman–Kac backward diffusion equation and published LevyStochCalc Brownian ItoL2CompletionMaster

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem FeynmanKac.space_time_ito_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsC12 u)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (r : ℝ),
      H ω r =
        if r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime) then
          m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) *
            deriv (fun x => u x (m.initialTime + r))
              (m.path (m.initialTime + r) ω)
        else 0)
    (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration H)
    (hq : ∀ (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
        (‖H ω r‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
    (s : ℝ) (hs : s ∈ Set.Icc m.initialTime m.terminalTime) :
    (fun ω => u (m.path s ω) s - u m.initialState m.initialTime) =ᵐ[P]
      (fun ω =>
        (∫ r in m.initialTime..s,
            deriv (fun q => u (m.path r ω) q) r +
            m.drift (m.path r ω) r * deriv (fun x => u x r) (m.path r ω) +
            (1 / 2 : ℝ) * (m.volatility (m.path r ω) r) ^ 2 *
              deriv (deriv (fun x => u x r)) (m.path r ω)) +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
          H hm hp hq (s - m.initialTime) ω) := by sorry
