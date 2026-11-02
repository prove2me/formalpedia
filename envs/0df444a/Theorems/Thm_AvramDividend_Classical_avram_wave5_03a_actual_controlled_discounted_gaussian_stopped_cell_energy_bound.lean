-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_energy_bound
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:01:43.618131+00:00
-- url     : https://prove2.me/theorems/c7822805-014d-4d3e-bfed-b7ece10041cc
-- title:
--   Actual controlled discounted strict-prepayment Gaussian stopped cell has exact L2 energy bound
-- statement:
--   For the actual source pure-Gaussian Lévy process with an original-filtration admissible dividend control and a C2 test function on the finite-cap interior, the exact original prepayment left-limit clipped gradient times exp(-qs)*sigma has stopped-cell squared L2 energy bounded by its deterministic squared clipping constant times the genuine same-source stopped Gaussian exponential quotient energy. The bound is an explicit formula exp(h sigma² theta²)-1 over theta². This builds directly from Proved source bounded-weight energy and Proved controlled strong predictability, and is a quantitative importable controlled Gaussian localisation estimate for Chat03.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weight_energy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_energy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (s : ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    let Z : Ω → ℝ := fun ω =>
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ
    (∫ ω, (H ω * Z ω) ^ 2 ∂P) ≤
      (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
        ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / (θ * θ)) := by
  sorry
