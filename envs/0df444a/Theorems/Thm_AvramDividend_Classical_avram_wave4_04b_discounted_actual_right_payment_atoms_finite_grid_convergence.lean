-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_actual_right_payment_atoms_finite_grid_convergence
-- name    : AvramDividend.Classical.avram_wave4_04b_discounted_actual_right_payment_atoms_finite_grid_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:34:31.223773+00:00
-- url     : https://prove2.me/theorems/6eb2c50b-4be2-462b-b9a1-0ba0b02527ae
-- title:
--   Full actual discounted right-payment atom reward is uniformly approximated by sufficiently large finite payment grids
-- statement:
--   For the true complete positive right-payment atom support of an arbitrary dividend strategy on [0,T], including the time-zero atom, the discounted real payment sum is finite and its arbitrary finite-grid partial sums converge to the entire series. Precisely, for every positive error tolerance there exists a finite set of actual right-payment times whose every finite superset has sum within that tolerance of the full countable sum. This supplies the genuine control-atomic finite-grid limit needed in a later stochastic Itô–Meyer passage; diffuse absolutely continuous and singular-continuous dividends remain separate and are not falsely assumed atomic.
-- source:
--   04-B finite-grid convergence on exact source Stieltjes right-payment support, deduced from Proved complete right-atom summability

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_discounted_actual_right_payment_atoms_finite_grid_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    let f : A → ℝ := fun s =>
      Real.exp (-(q * (s : ℝ))) *
        (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)
    ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, ∀ G : Finset A, F ⊆ G →
        |(∑ s ∈ G, f s) - (∑' s : A, f s)| < ε := by
  sorry
