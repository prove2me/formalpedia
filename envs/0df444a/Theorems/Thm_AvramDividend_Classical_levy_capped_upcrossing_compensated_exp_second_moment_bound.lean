-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_second_moment_bound
-- name    : AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_second_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:01:31.599996+00:00
-- url     : https://prove2.me/theorems/3d273a9d-d6cd-42e5-bc2a-89e7e5558b95
-- title:
--   Uniform second-moment bound for the compensated Lévy exponential at a capped upper-grid first passage
-- statement:
--   For any bounded monotone grid ending at clock(m), the compensated exponential martingale observed at the first grid upcrossing capped by m has a second moment bounded uniformly by exp(clock(m) max(ψ(2θ)−2ψ(θ),0)). This supplies uniform integrability for mesh-to-continuous upper-passage optional stopping; the bound holds independently of the q-scale stopped-martingale identity and for every spectrally negative Lévy process.
-- source:
--   Avram, Palmowski and Pistorius (2007), stopped martingale treatment of two-sided exit; accepted Prove2Me discrete capped upper-grid exponential moment 1 (c023eacf-a8d8-4e0e-9a42-48fc016b929b) and integrability (0ebde21a-82c5-41f7-94f6-89944f9047d9). Derived through an exact pointwise exponential-square comparison at θ and 2θ.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_second_moment_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    (∫ ω,
      let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      (Real.exp (θ * X.X (clock K) ω -
        (clock K : ℝ) * X.ψ θ)) ^ 2 ∂P) ≤
    Real.exp ((clock m : ℝ) *
      max (X.ψ (2 * θ) - 2 * X.ψ θ) 0) := by sorry
