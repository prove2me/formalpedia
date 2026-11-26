-- Prove2me | solution 1 for section5_discrete_position_evolution
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:03:45.783038+00:00
-- url     : https://prove2.me/submissions/1ba283d7-54d4-4e71-8d80-79db763b5f03

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_linear_phase_unitary
import Theorems.Thm_section5_phase_list_unitary
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











theorem section5_single_phase_embedded {n : ℕ} (i : Fin n) (t : ℝ) :
    embedOp (section5_single_phase_gate i t).gate.mat (section5_single_phase_gate i t).wires =
      Matrix.diagonal (fun z => section5_phase (if z i then t else 0)) := by
  dsimp only [section5_single_phase_gate]
  rw [section5_embed_diagonal]
  rfl

theorem section5_pair_phase_embedded {n : ℕ} (i j : Fin n) (h : i ≠ j) (t : ℝ) :
    embedOp (section5_pair_phase_gate i j h t).gate.mat (section5_pair_phase_gate i j h t).wires =
      Matrix.diagonal (fun z => section5_phase (if z i && z j then t else 0)) := by
  dsimp only [section5_pair_phase_gate]
  rw [section5_embed_diagonal]
  rfl



theorem section5_monomial_phase_embedded {n : ℕ} (i j : Fin n) (t : ℝ) :
    embedOp (section5_monomial_phase_gate i j t).gate.mat (section5_monomial_phase_gate i j t).wires =
      Matrix.diagonal (fun z => section5_phase (if z i && z j then t else 0)) := by
  classical
  by_cases h : i = j
  · subst j
    have hg : section5_monomial_phase_gate i i t = section5_single_phase_gate i t := by
      unfold section5_monomial_phase_gate
      exact dif_pos rfl
    rw [hg]
    simpa only [Bool.and_self] using section5_single_phase_embedded i t
  · have hg : section5_monomial_phase_gate i j t = section5_pair_phase_gate i j h t := by
      unfold section5_monomial_phase_gate
      exact dif_neg h
    rw [hg]
    exact section5_pair_phase_embedded i j h t





theorem section5_quadratic_phase_size (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (section5_quadratic_phase_circuit n a t).size = n^2 := by
  classical
  simp [section5_quadratic_phase_circuit, Circuit.size, pow_two]

theorem section5_quadratic_phase_unitary (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (section5_quadratic_phase_circuit n a t).unitary =
      Matrix.diagonal (fun z => section5_phase (t*(∑ i : Fin n, if z i then a i else 0)^2)) := by
  classical
  have hh := section5_phase_list_unitary
    (Finset.univ : Finset (Fin n×Fin n)).toList
    (fun p => section5_monomial_phase_gate p.1 p.2 (t*a p.1*a p.2))
    (fun p z => if z p.1 && z p.2 then t*a p.1*a p.2 else 0)
    (fun p _ => section5_monomial_phase_embedded p.1 p.2 _)
  change Circuit.unitary ((Finset.univ : Finset (Fin n×Fin n)).toList.map
    (fun p => section5_monomial_phase_gate p.1 p.2 (t*a p.1*a p.2))) = _
  rw [hh]
  congr 1
  funext z
  congr 1
  rw [Finset.sum_map_toList, Fintype.sum_prod_type]
  have hterm (i j : Fin n) : (if z i && z j then t*a i*a j else 0) =
      t*(if z i then a i else 0)*(if z j then a j else 0) := by
    cases z i <;> cases z j <;> simp
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring





theorem section5_linear_phase_size (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (section5_linear_phase_circuit n a t).size = n := by
  classical
  simp [section5_linear_phase_circuit, Circuit.size]





theorem section5_global_phase_embedded {n : ℕ} (hn : 0 < n) (t : ℝ) :
    embedOp (section5_global_phase_gate hn t).gate.mat (section5_global_phase_gate hn t).wires =
      Matrix.diagonal (fun _ => section5_phase t) := by
  dsimp only [section5_global_phase_gate]
  rw [section5_embed_diagonal]

theorem section5_phase_circuit_append {n : ℕ} (c d : Circuit gates12 n) :
    (c++d).unitary = d.unitary*c.unitary := by
  simp [Circuit.unitary, List.reverse_append, List.prod_append]



theorem section5_centered_quadratic_size (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (c t : ℝ) :
    (section5_centered_quadratic_circuit n hn a c t).size = n^2+n+1 := by
  unfold section5_centered_quadratic_circuit
  have hq := section5_quadratic_phase_size n a t
  have hl := section5_linear_phase_size n a (-2*t*c)
  unfold Circuit.size at hq hl
  simp only [Circuit.size, List.length_append, List.length_singleton]
  rw [hq, hl]

theorem section5_centered_quadratic_unitary (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (c t : ℝ) :
    (section5_centered_quadratic_circuit n hn a c t).unitary =
      Matrix.diagonal (fun z => section5_phase (t*((∑ i : Fin n, if z i then a i else 0)-c)^2)) := by
  classical
  unfold section5_centered_quadratic_circuit
  rw [section5_phase_circuit_append, section5_phase_circuit_append,
    section5_quadratic_phase_unitary, section5_linear_phase_unitary]
  have hglobal : Circuit.unitary [section5_global_phase_gate hn (t*c^2)] =
      Matrix.diagonal (fun _ => section5_phase (t*c^2)) := by
    simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    exact section5_global_phase_embedded hn _
  rw [hglobal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext z
  rw [← section5_phase_add, ← section5_phase_add]
  congr 1
  ring



theorem section5_bitsValue_as_real_sum {q : ℕ} (z : Qubits q) :
    (QuantumLTF.Example.bitsValue z : ℝ) =
      ∑ i : Fin q, if z i then ((2 ^ (q-1-i.val) : ℕ) : ℝ) else 0 := by
  classical
  simp only [QuantumLTF.Example.bitsValue, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem solution (q : ℕ) (hq : 0 < q) (t : ℝ) :
    ∃ circ : Circuit gates12 q, circ.size = q^2+q+1 ∧
      circ.unitary = Matrix.diagonal (fun z =>
        section5_phase (t * QuantumLTF.Example.scalarGrid z ^ 2)) := by
  let a : Fin q → ℝ := fun i => ((2 ^ (q-1-i.val) : ℕ) : ℝ)
  let c : ℝ := ((2 ^ (q-1) : ℕ) : ℝ)
  let δ : ℝ := Real.sqrt (4 * Real.pi / 2^q)
  refine ⟨section5_centered_quadratic_circuit q hq a c (t*δ^2),
    section5_centered_quadratic_size q hq a c (t*δ^2), ?_⟩
  rw [section5_centered_quadratic_unitary]
  congr 1
  funext z
  congr 1
  rw [← section5_bitsValue_as_real_sum]
  change t*δ^2*((QuantumLTF.Example.bitsValue z : ℝ)-c)^2 =
    t*(((QuantumLTF.Example.bitsValue z : ℝ)-c)*δ)^2
  ring
