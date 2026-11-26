-- Prove2me | solution 1 for section5_grid_sampling_integral
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:23.430009+00:00
-- url     : https://prove2.me/submissions/33de38f4-b11d-4d3c-ad3a-026644352a27

import Definitions.Def_Section5Verified_Section5CellQuadrature
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
theorem solution {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    (∫ x in a..(a+N*δ), ‖f x-f (section5_grid_sample a δ x)‖^2) =
      ∑ j ∈ Finset.range N,
        ∫ x in (a+j*δ)..(a+(j+1)*δ), ‖f x-f (a+j*δ)‖^2 := by
  let F := fun x => ‖f x-f (section5_grid_sample a δ x)‖^2
  have hle (j : ℕ) : a+(j:ℝ)*δ ≤ a+(j+1)*δ := by linarith
  have heq (j : ℕ) : Set.EqOn (fun x => ‖f x-f (a+j*δ)‖^2) F
      (Set.uIoo (a+j*δ) (a+(j+1)*δ)) := by
    intro x hx
    rw [Set.uIoo_of_le (hle j)] at hx
    dsimp only [F]
    rw [section5_grid_sample_on_cell a δ hδ j x ⟨hx.1.le,hx.2⟩]
  have hint (j : ℕ) : IntervalIntegrable F volume (a+j*δ) (a+(j+1)*δ) :=
    ((((hf.sub continuous_const).norm).pow 2).intervalIntegrable _ _).congr_uIoo (heq j)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => a+j*δ) (n := N) (f := F) (μ := volume)
    (fun j _ => by simpa only [Nat.cast_add, Nat.cast_one] using hint j)
  have hsum' : (∫ x in a..(a+N*δ), F x) =
      ∑ j ∈ Finset.range N, ∫ x in (a+j*δ)..(a+(j+1)*δ), F x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using hsum.symm
  rw [hsum']
  apply Finset.sum_congr rfl
  intro j hj
  exact intervalIntegral.integral_congr_uIoo (heq j).symm
