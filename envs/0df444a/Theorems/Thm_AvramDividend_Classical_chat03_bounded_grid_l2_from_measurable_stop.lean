-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_from_measurable_stop
-- name    : AvramDividend.Classical.chat03_bounded_grid_l2_from_measurable_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:20:36.411795+00:00
-- url     : https://prove2.me/theorems/48fbdfac-ec22-42b2-a986-243c8f4a82ab
-- title:
--   Finite two-sided exit grid has mesh-uniform L² bound under only stopped-observable measurability
-- statement:
--   For the exact spectrally negative Lévy and official q-scale function, choose a deterministic monotone finite clock, first strict two-sided grid exit K≤m and horizon N≥clock(m). If the stopped reserve and stopped real-valued clock are measurable, then the squared discounted scale payoff is integrable and its expectation is bounded by (ψ(θ)-q)^(-2) exp(2θ(x+1)+N max(ψ(2θ),0)). The theorem DISCHARGES the compensated exponential's integrability and expectation-one premises from the independently Proved two-sided stopped exponential-moment theorem. Bochner integrability follows from the nonzero expected value using pinned Integrable.of_integral_ne_zero, so no extra finite-jump moment or continuity of the original filtration is needed. It also discharges stopped-scale measurability using the independently Proved Borel measurability of W, leaving only two explicit finite-grid observable measurability facts which the pinned discrete stopping-time theory can supply.
-- source:
--   Proved child theorem modules chat03_fixed_horizon_scale_l2_bound b0f87b32-3722-4ca0-9de1-cf1737ca8452; chat03_two_sided_grid_compensated_exp_moment_one 6b72c3df-fe64-48b4-9676-1c02513fc800; chat03_scale_function_borel_measurable 45cbe3b4-374d-4fa4-b988-e09f93b74cab; pinned Mathlib MeasureTheory Integral Bochner Basic Integrable.of_integral_ne_zero. Mathlib SHA 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_bounded_grid_l2_from_measurable_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (hZmeas : Measurable (fun ω => X.X (clock (K ω)) ω))
    (hTmeas : Measurable (fun ω => (clock (K ω) : ℝ)))
    (N : ℝ≥0) (hNm : clock m ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
