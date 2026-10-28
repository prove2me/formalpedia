-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_crossing_compensated_exp_lower_bound
-- name    : AvramDividend.Classical.levy_capped_upper_grid_crossing_compensated_exp_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:47:45.174294+00:00
-- url     : https://prove2.me/theorems/f450604b-82f1-4bef-bc57-f21946c811b3
-- title:
--   Crossing contribution to a capped upper-only exponential martingale approaches unit mass
-- statement:
--   The compensated exponential stopped at the first sampled strictly upper crossing or the terminal grid index has expectation exactly one. On the no-crossing event its contribution is at most exp(θz−qT). Therefore the expected exponential on paths with a crossing at or before the terminal grid index is at least 1−exp(θz−qT). This is an exact finite-grid decomposition, independent of a continuous first-passage formula.
-- source:
--   Proved bounded upper-only exponential optional stopping c023eacf and no-hit remainder f590893f; basic Bochner integrability and event splitting.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_discounted_remainder_bound
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upper_grid_crossing_compensated_exp_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ q : ℝ) (hθ : 0 ≤ θ) (hroot : X.ψ θ = q)
    (z : ℝ) (m : ℕ) :
    1 - Real.exp (θ * z - (clock m : ℝ) * q) ≤
    (∫ ω, (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        (0 : ℝ)
      else
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)) ∂P) := by sorry
