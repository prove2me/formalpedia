-- Prove2me | solution 1 for section5_elementary_centered_qft
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:03:47.891488+00:00
-- url     : https://prove2.me/submissions/6d9f114e-80af-497f-acbe-fdd3482fae65

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_elementary_qft
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_linear_phase_unitary
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact Fourier transforms in the mission's elementary gate set, reusing the
accepted QFT construction, and the centered Fourier convention for the QHO. -/















theorem section5_centered_fourier_factorization (q : ℕ) (hq : 0 < q) :
    section5_centered_fourier q=
      Matrix.diagonal (fun _ => section5_phase (Real.pi*((2^(q-1):ℕ):ℝ))) *
        Matrix.diagonal (fun y => section5_phase (-Real.pi*(bitsToNat y:ℝ))) *
          qftQubits q * Matrix.diagonal (fun z => section5_phase (-Real.pi*(bitsToNat z:ℝ))) := by
  classical
  have hpow : (2:ℂ)^q=2*((2^(q-1):ℕ):ℂ) := by
    have hh : (2:ℕ)^q=2*2^(q-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hq,pow_succ]
      ring
    exact_mod_cast hh
  have hne : (2:ℂ)^q ≠ 0 := pow_ne_zero _ (by norm_num)
  ext y z
  simp only [section5_centered_fourier,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.diagonal_mul_diagonal,qftQubits,qftMatrix,Matrix.submatrix_apply,Matrix.of_apply,
    bitsEquivFin_apply,section5_phase]
  push_cast at hpow ⊢
  rw [← mul_div_assoc,div_mul_eq_mul_div,← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
  congr 2
  field_simp
  rw [hpow]
  ring



end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-!
Quadratic phase circuits used in Jain--Iyer--Somma--Bao--Jordan,
Efficient Quantum Hermite Transform, arXiv:2510.04929, Section 3.1.
The arbitrary one- and two-qubit gate model permits exact phase angles.
-/





@[simp] theorem section5_phase_zero : section5_phase 0 = 1 := by simp [section5_phase]































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













end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (q : ℕ) (hq : 0 < q) :
    ∃ c : Circuit gates12 q, c.size ≤ q^2+2*q+1 ∧ c.unitary=section5_centered_fourier q := by
  classical
  let a : Fin q → ℝ := fun i => ((2^(q-1-i.val):ℕ):ℝ)
  let d := section5_linear_phase_circuit q a (-Real.pi)
  have hdsize : d.size=q := section5_linear_phase_size q a (-Real.pi)
  have hdu : d.unitary=Matrix.diagonal (fun z => section5_phase (-Real.pi*(bitsToNat z:ℝ))) := by
    rw [section5_linear_phase_unitary]
    congr 1
    funext z
    congr 1
    rw [show (bitsToNat z:ℝ)=∑ i : Fin q,if z i then a i else 0 by
      simp [bitsToNat,a]]
  obtain ⟨c,hcs,hcu⟩ := section5_elementary_qft q
  let g := section5_global_phase_gate hq (Real.pi*((2^(q-1):ℕ):ℝ))
  refine ⟨d++c++d++[g],?_,?_⟩
  · simp only [Circuit.size,List.length_append,List.length_singleton]
    change d.length=q at hdsize
    change c.length ≤ q^2 at hcs
    omega
  · simp only [section5_phase_circuit_append,hdu,hcu]
    have hg : Circuit.unitary [g]=Matrix.diagonal
        (fun _ => section5_phase (Real.pi*((2^(q-1):ℕ):ℝ))) := by
      simp only [Circuit.unitary,List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,
        List.nil_append,List.prod_cons,List.prod_nil,mul_one]
      exact section5_global_phase_embedded hq _
    rw [hg,← mul_assoc,← mul_assoc,← section5_centered_fourier_factorization q hq]
