-- Prove2me | solution 1 for section5_complex_matrix_product_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:16.355334+00:00
-- url     : https://prove2.me/submissions/1a884d69-da18-4660-b541-1abe37e7dcf9

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_batched_bilinear_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A signed bilinear circuit with coefficients that may vary by summand. This
includes both components of complex matrix multiplication: use 2*n summands,
with negative coefficients on the imaginary-imaginary real-part contribution. -/









theorem section5_integer_bit_value_neg {a : ℕ} (c : Fin a → ℤ) (x : Qubits a) :
    section5_integer_bit_value (fun i => -c i) x= -section5_integer_bit_value c x := by
  unfold section5_integer_bit_value
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp



end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A full complex integer matrix multiplication compiled to the actual reversible
gate set. The input and shared workspace are preserved. -/













theorem section5_complex_mul_expansion {r n a b : ℕ}
    (c : Fin a → ℤ) (d : Fin b → ℤ)
    (Are Aim : Fin n → Fin n → Fin a → Fin r)
    (Bre Bim : Fin n → Fin n → Fin b → Fin r)
    (i : Fin (2*n*n)) (z : Qubits r) :
    (∑ k : Fin (n+n),section5_integer_bit_value (section5_complex_mul_coeff c i k)
      (z ∘ section5_complex_mul_u Are Aim i k)*
      section5_integer_bit_value d (z ∘ section5_complex_mul_x Bre Bim i k))=
        section5_complex_product_component (section5_read_integer_matrix c Are Aim z)
          (section5_read_integer_matrix d Bre Bim z) (section5_complex_entry_index n i) := by
  cases hcomp : (section5_complex_entry_index n i).1
  · simp only [section5_complex_mul_coeff,section5_complex_mul_x,section5_complex_mul_u,
      hcomp,Bool.false_eq_true,↓reduceIte]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,section5_integer_bit_value_neg,
      neg_mul,Finset.sum_neg_distrib]
    simp only [section5_complex_product_component,hcomp,Bool.false_eq_true,↓reduceIte,
      Section5IntegerMatrix.mul,section5_read_integer_matrix,Matrix.sub_apply,Matrix.mul_apply]
    rfl
  · simp only [section5_complex_mul_coeff,section5_complex_mul_x,section5_complex_mul_u,
      hcomp,↓reduceIte]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right]
    simp only [section5_complex_product_component,hcomp,↓reduceIte,Section5IntegerMatrix.mul,
      section5_read_integer_matrix,Matrix.add_apply,Matrix.mul_apply]
    rfl









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m r n a b w : ℕ}
    (data : Fin r → Fin m) (c : Fin a → ℤ) (d : Fin b → ℤ)
    (Are Aim : Fin n → Fin n → Fin a → Fin r)
    (Bre Bim : Fin n → Fin n → Fin b → Fin r)
    (p : Fin (2*n*n) → Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ ((16*w+6)*((n+n)*a*b))*(2*n*n) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ZMod (2^w))=
            (section5_complex_product_component
              (section5_read_integer_matrix c Are Aim (z ∘ data))
              (section5_read_integer_matrix d Bre Bim (z ∘ data))
              (section5_complex_entry_index n i):ZMod (2^w)) := by
  obtain ⟨circ,hsize,hact⟩ := section5_batched_bilinear_circuit data
    (section5_complex_mul_u Are Aim) (section5_complex_mul_x Bre Bim)
    (section5_complex_mul_coeff c) (fun _ _ => d) p anc t hpair hdata hpa htp hta hdt
  refine ⟨circ,hsize,?_⟩
  intro z hzt hza hz0
  obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hza hz0
  refine ⟨z',hz',hoff,?_⟩
  intro i
  have hh := hval i
  have he := section5_complex_mul_expansion c d Are Aim Bre Bim i (z ∘ data)
  exact hh.trans (congrArg (fun v : ℤ => (v:ZMod (2^w))) he)
