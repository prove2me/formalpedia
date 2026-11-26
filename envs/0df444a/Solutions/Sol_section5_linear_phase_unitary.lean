-- Prove2me | solution 1 for section5_linear_phase_unitary
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:47.076506+00:00
-- url     : https://prove2.me/submissions/02606053-7754-4bc0-9110-b388914cc548

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_phase_list_unitary
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-!
Quadratic phase circuits used in Jain--Iyer--Somma--Bao--Jordan,
Efficient Quantum Hermite Transform, arXiv:2510.04929, Section 3.1.
The arbitrary one- and two-qubit gate model permits exact phase angles.
-/

















theorem section5_single_phase_embedded {n : ℕ} (i : Fin n) (t : ℝ) :
    embedOp (section5_single_phase_gate i t).gate.mat (section5_single_phase_gate i t).wires =
      Matrix.diagonal (fun z => section5_phase (if z i then t else 0)) := by
  dsimp only [section5_single_phase_gate]
  rw [section5_embed_diagonal]
  rfl









































end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (section5_linear_phase_circuit n a t).unitary =
      Matrix.diagonal (fun z => section5_phase (t*(∑ i : Fin n, if z i then a i else 0))) := by
  classical
  have hh := section5_phase_list_unitary (Finset.univ : Finset (Fin n)).toList
    (fun i => section5_single_phase_gate i (t*a i))
    (fun i z => if z i then t*a i else 0)
    (fun i _ => section5_single_phase_embedded i _)
  change Circuit.unitary ((Finset.univ : Finset (Fin n)).toList.map
    (fun i => section5_single_phase_gate i (t*a i))) = _
  rw [hh]
  congr 1
  funext z
  congr 1
  rw [Finset.sum_map_toList, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases z i <;> simp
