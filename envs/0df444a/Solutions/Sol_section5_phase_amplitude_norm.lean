-- Prove2me | solution 1 for section5_phase_amplitude_norm
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:52.041027+00:00
-- url     : https://prove2.me/submissions/58f6a11d-26c8-4f0c-903d-fbbde0886f40

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Mathlib
section
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example









theorem section5_ltf_label_value {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) :
    ((ltf w 0 x : ℤ):ℂ) = if decide (ltf w 0 x = -1) then -1 else 1 := by
  unfold ltf sgn
  simp only [sub_zero]
  by_cases h : 0 ≤ inner ℝ w x
  · simp [h,not_lt_of_ge h]
  · simp [h,lt_of_not_ge h]



theorem section5_grid_amplitude_norm {n q : ℕ} :
    ‖(WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))‖ = 1 := by
  have hpos (x : Qubits (n*q)) : 0 < gridWeight x := Real.exp_pos _
  have hZ : 0 < ∑ z : Qubits (n*q), gridWeight z :=
    Finset.sum_pos (fun z _ => hpos z) Finset.univ_nonempty
  have hsq : ‖(WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [section5_grid_amplitude, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg (hpos _).le hZ.le)]
    rw [← Finset.sum_div,div_self hZ.ne']
  nlinarith [norm_nonneg (WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
theorem solution {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))‖ = 1 := by
  have hn : ∀ x : Qubits (n*q), ‖(ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x‖ =
      ‖section5_grid_amplitude x‖ := by
    intro x
    rw [norm_mul,section5_ltf_label_value]
    split_ifs <;> simp
  have hsq : ‖(WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hn]
    exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)))).symm.trans
      (by rw [section5_grid_amplitude_norm]; norm_num)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))]
