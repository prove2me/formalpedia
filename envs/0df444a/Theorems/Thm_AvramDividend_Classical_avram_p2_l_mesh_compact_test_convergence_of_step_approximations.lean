-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_convergence_of_step_approximations
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_convergence_of_step_approximations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:32:15.377645+00:00
-- url     : https://prove2.me/theorems/f4db1df6-ed16-438f-b4af-05b7ce6669ca
-- title:
--   Full original-grid compact-test convergence from explicit uniformly dense step approximations
-- statement:
--   A genuine cadlag path on a finite horizon has original T/(n+1) grid marked-test sums converging to the finite intrinsic jump sum for any negative-supported real test with an explicit independently dischargeable uniform finite interval-step approximation property. All approximant boundaries avoid the finitely many significant original marks; no desired convergence, Borel indicator limit, surrogate process or cutoff-atom-free law is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_step_approximation_eventual_error

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_convergence_of_step_approximations
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -ρ < z → f z = 0)
    (hApprox : ∀ η : ℝ, 0 < η →
      ∃ m : ℕ, ∃ a b c : Fin m → ℝ,
        (∀ i, b i ≤ -ρ) ∧
        (∀ (i : Fin m) (u : ℝ≥0), 0 < u → u ≤ T →
          ρ ≤ |Y u - Function.leftLim Y u| →
          Y u - Function.leftLim Y u ≠ a i ∧
            Y u - Function.leftLim Y u ≠ b i) ∧
        (∀ z : ℝ,
          |f z - (∑ i : Fin m,
            if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η)) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
