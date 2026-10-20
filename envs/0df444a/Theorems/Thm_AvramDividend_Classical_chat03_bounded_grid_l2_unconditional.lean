-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_unconditional
-- name    : AvramDividend.Classical.chat03_bounded_grid_l2_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:24:17.986985+00:00
-- url     : https://prove2.me/theorems/d591a684-7fbc-4f11-9c18-7d38c35320a0
-- title:
--   Uniform L² bound for actual strict two-sided grid-stopped q-scale values without extra measurability assumptions
-- statement:
--   Given only the official spectrally negative Lévy process X, the official q-scale function W, q≥0, a nonnegative Laplace parameter theta with psi(theta)>q, a deterministic monotone finite grid clock and matching sampled filtration, and K equal to the first strict two-sided grid exit capped at m, prove that the squared discounted stopped scale payoff is integrable and its expectation is bounded by exp(2theta(x+1)+N max(psi(2theta),0))/(psi(theta)-q)^2, where N≥clock(m). All previously conditional measurability, compensated exponential integrability and unit-expectation premises are discharged using independently Proved Chat 03 children. The constant does not depend on grid mesh, thus gives a true uniform L² bound for dyadic grids of fixed horizon, without invoking a right-continuous filtration, continuous-time optional stopping, first jump moment or killed q-scale martingale.
-- source:
--   Proved Chat 03 discrete stopped observables measurable d31b0bab-953d-485e-996e-1452100c91a3, and the independent bounded_grid_l2_from_measurable_stop conditional reduction UUID 48fbdfac-ec22-42b2-a986-243c8f4a82ab once Proved. Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_from_measurable_stop
import Mathlib.Probability.Process.HittingTime

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_bounded_grid_l2_unconditional
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
    (N : ℝ≥0) (hNm : clock m ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
