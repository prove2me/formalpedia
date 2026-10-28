-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_deterministic_horizon_scale_l2_uniform_bound
-- name    : AvramDividend.Classical.chat04_deterministic_horizon_scale_l2_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:44:24.915634+00:00
-- url     : https://prove2.me/theorems/19551a5a-42f2-4b72-baef-9be2f24a4bfc
-- title:
--   Uniform second-moment bound for deterministic-horizon Lévy q-scale rewards
-- statement:
--   For a spectrally negative Lévy process with a positive Laplace gap at θ, the squared discounted q-scale payoff at any deterministic time t≤N is integrable, with an explicit upper bound independent of t. This supplies an L² envelope over bounded time intervals and is a central route to uniform integrability and time-zero expectation continuity for the killed q-scale semigroup.
-- source:
--   Exact Proved import chain: fixed-horizon L² estimate b0f87b32, Borel measurable scale 45cbe3b4, compensated exponential mean invariance 5660f5e2, and deterministic exponential integrability dd773186. Next needed for terminal-only expectation convergence and the Open killed harmonicity a885f0b3 and stopped exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_mean_invariance
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_deterministic_horizon_scale_l2_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (htN : t ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (t : ℝ))) *
      W (x + X.X t ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
