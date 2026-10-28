-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_square_integrable
-- name    : AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:16:18.14285+00:00
-- url     : https://prove2.me/theorems/537b7855-7bf3-4c48-8ed6-109fca99c2a7
-- title:
--   Square integrability of the compensated Lévy exponential at a capped upper-only grid passage
-- statement:
--   For a sampled spectrally negative Lévy process on any nondecreasing grid, the square of its compensated positive-Laplace exponential evaluated at a capped first sampled upcrossing is Bochner integrable. This is an essential L² fact: a real Bochner integral's numerical bound alone does not certify integrability. It combines stopped exponential integrability at θ and 2θ, a pathwise square-domination inequality, and AEStronglyMeasurable closure.
-- source:
--   Avram, Palmowski and Pistorius (2007), stopped exponential Lévy martingale; independently accepted Prove2Me upper-grid stopped exponential integrability 0ebde21a-82c5-41f7-94f6-89944f9047d9. Distinct from the separately Proved integral inequality 3d273a9d-d6cd-42e5-bc2a-89e7e5558b95, because Lean's Bochner integral returns zero when nonintegrable.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    Integrable (fun ω =>
      let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      (Real.exp (θ * X.X (clock K) ω -
        (clock K : ℝ) * X.ψ θ)) ^ 2) P := by sorry
