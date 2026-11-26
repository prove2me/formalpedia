-- Prove2me | solution 1 for section5_phase_list_unitary
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:56.377144+00:00
-- url     : https://prove2.me/submissions/94771684-ba23-46cd-97b7-fc67f1939fed

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-!
Quadratic phase circuits used in Jain--Iyer--Somma--Bao--Jordan,
Efficient Quantum Hermite Transform, arXiv:2510.04929, Section 3.1.
The arbitrary one- and two-qubit gate model permits exact phase angles.
-/



theorem section5_phase_add (s t : ℝ) : section5_phase (s+t) = section5_phase s*section5_phase t := by
  simp only [section5_phase, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem section5_phase_zero : section5_phase 0 = 1 := by simp [section5_phase]





















































end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {n : ℕ} {ι : Type*} (l : List ι)
    (g : ι → GateApp gates12 n) (t : ι → Qubits n → ℝ)
    (hg : ∀ i ∈ l, embedOp (g i).gate.mat (g i).wires =
      Matrix.diagonal (fun z => section5_phase (t i z))) :
    Circuit.unitary (l.map g) = Matrix.diagonal (fun z => section5_phase ((l.map (fun i => t i z)).sum)) := by
  classical
  induction l with
  | nil => simp [Circuit.unitary]
  | cons i l ih =>
    have htail := ih (fun j hj => hg j (List.mem_cons_of_mem i hj))
    have hhead := hg i (List.mem_cons_self)
    have hc : Circuit.unitary ((i::l).map g) = Circuit.unitary (l.map g) * embedOp (g i).gate.mat (g i).wires := by
      simp [Circuit.unitary, List.reverse_cons]
    rw [hc, htail, hhead, Matrix.diagonal_mul_diagonal]
    congr 1
    funext z
    simp only [List.map_cons, List.sum_cons, section5_phase_add]
    exact mul_comm _ _
