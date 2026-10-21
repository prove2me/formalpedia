-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_exp_bound
-- name    : AvramDividend.Classical.levy_grid_upper_exit_exp_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:27:28.83315+00:00
-- url     : https://prove2.me/theorems/ffcf762c-548c-4c76-9b78-e1247d592875
-- title:
--   Finite-grid Lévy upper-exit discount bound from the compensated stopped exponential
-- statement:
--   For the actual spectrally negative Lévy process stopped at an adapted finite two-sided grid exit, the accepted unit compensated exponential martingale moment and integrability yield a discounted upper-exit expectation at most exp(-θ upper), for θ≥0. The sole additional hypothesis is integrability of the upper-exit discounted payoff, to be supplied by separate finite-grid measurability and boundedness results. The theorem is a genuine stochastic finite-grid input to the continuous first-passage and Esscher monotonicity argument.
-- source:
--   Proved chat03_two_sided_grid_compensated_exp_integrable and chat03_two_sided_grid_compensated_exp_moment_one; current generic stopped exponential upper-exit inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_grid_upper_exit_exp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω)
    (hpart : Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp
          (-((clock (K ω)) : ℝ) * X.ψ θ))) P) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by sorry
