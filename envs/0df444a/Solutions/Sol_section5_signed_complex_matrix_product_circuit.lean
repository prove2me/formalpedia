-- Prove2me | solution 1 for section5_signed_complex_matrix_product_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:36.478545+00:00
-- url     : https://prove2.me/submissions/21cae689-3fd1-4dac-90c3-263108239037

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
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_complex_matrix_product_circuit
import Theorems.Thm_section5_integer_matrix_product_bound
import Theorems.Thm_section5_twos_complement_decode_mod
import Theorems.Thm_section5_twos_complement_residue
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A complete signed dot-product comparator with an explicit polynomial gate bound.
The accumulator width below is deliberately generous, to make overflow impossible. -/

theorem section5_signed_residue_range (H z : ℤ) (hH : 0 < H) :
    -H ≤ section5_signed_residue H z ∧ section5_signed_residue H z < H := by
  have hlo := Int.emod_nonneg z (by positivity : 2*H ≠ 0)
  have hhi := Int.emod_lt_of_pos z (by positivity : 0 < 2*H)
  unfold section5_signed_residue
  split_ifs <;> constructor <;> omega

theorem section5_twos_complement_abs (b : ℕ) (z : Qubits (b+1)) :
    |section5_integer_bit_value (section5_twos_coefficient (b+1)) z| ≤ (2:ℤ)^b := by
  rw [section5_twos_complement_residue]
  have hh := section5_signed_residue_range ((2:ℤ)^b) (bitsToNatLSB z) (by positivity)
  exact abs_le.mpr ⟨hh.1,hh.2.le⟩





end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A full complex integer matrix multiplication compiled to the actual reversible
gate set. The input and shared workspace are preserved. -/

















theorem section5_complex_matrix_gate_bound (n a b w : ℕ) (hw : 1 ≤ w) :
    ((16*w+6)*((n+n)*a*b))*(2*n*n) ≤ 88*w*n^3*a*b := by
  have hh : 16*w+6 ≤ 22*w := by omega
  calc
    _ ≤ (22*w)*((n+n)*a*b)*(2*n*n) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hh)
    _ = _ := by ring

theorem section5_signed_complex_product_no_overflow {r n a b : ℕ}
    (Are Aim : Fin n → Fin n → Fin (a+1) → Fin r)
    (Bre Bim : Fin n → Fin n → Fin (b+1) → Fin r)
    (z : Qubits r) (i : Bool × Fin n × Fin n) :
    |section5_complex_product_component
      (section5_read_integer_matrix (section5_twos_coefficient (a+1)) Are Aim z)
      (section5_read_integer_matrix (section5_twos_coefficient (b+1)) Bre Bim z) i| <
        (2:ℤ)^(2*n+a+b) := by
  let A := section5_read_integer_matrix (section5_twos_coefficient (a+1)) Are Aim z
  let B := section5_read_integer_matrix (section5_twos_coefficient (b+1)) Bre Bim z
  have hA : A.Bounded ((2:ℤ)^a) :=
    ⟨fun i j => section5_twos_complement_abs a (z ∘ Are i j),
      fun i j => section5_twos_complement_abs a (z ∘ Aim i j)⟩
  have hB : B.Bounded ((2:ℤ)^b) :=
    ⟨fun i j => section5_twos_complement_abs b (z ∘ Bre i j),
      fun i j => section5_twos_complement_abs b (z ∘ Bim i j)⟩
  have hprod := section5_integer_matrix_product_bound A B ((2:ℤ)^a) ((2:ℤ)^b)
    (by positivity) (by positivity) hA hB
  have hc : |section5_complex_product_component A B i| ≤ 2*n*(2:ℤ)^a*(2:ℤ)^b := by
    unfold section5_complex_product_component
    split_ifs
    · exact hprod.2 _ _
    · exact hprod.1 _ _
  have hn : 2*(n:ℤ) < (2:ℤ)^(2*n) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=2*n))
  have hpow : 2*(n:ℤ)*(2:ℤ)^a*(2:ℤ)^b < (2:ℤ)^(2*n+a+b) := by
    rw [pow_add,pow_add]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hn (by positivity)) (by positivity)
  exact hc.trans_lt hpow



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m r n a b : ℕ}
    (data : Fin r → Fin m)
    (Are Aim : Fin n → Fin n → Fin (a+1) → Fin r)
    (Bre Bim : Fin n → Fin n → Fin (b+1) → Fin r)
    (p : Fin (2*n*n) → Fin (2*n+a+b+1) ↪ Fin m)
    (anc : Fin (2*n+a+b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 88*(2*n+a+b+1)*n^3*(a+1)*(b+1) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, section5_integer_bit_value (section5_twos_coefficient (2*n+a+b+1)) (z' ∘ p i)=
            section5_complex_product_component
              (section5_read_integer_matrix (section5_twos_coefficient (a+1)) Are Aim (z ∘ data))
              (section5_read_integer_matrix (section5_twos_coefficient (b+1)) Bre Bim (z ∘ data))
              (section5_complex_entry_index n i) := by
  obtain ⟨circ,hsize,hact⟩ := section5_complex_matrix_product_circuit data
    (section5_twos_coefficient (a+1)) (section5_twos_coefficient (b+1))
    Are Aim Bre Bim p anc t hpair hdata hpa htp hta hdt
  refine ⟨circ,hsize.trans (section5_complex_matrix_gate_bound _ _ _ _ (by omega)),?_⟩
  intro z hzt hza hz0
  obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hza hz0
  refine ⟨z',hz',hoff,?_⟩
  intro i
  have hbnd := section5_signed_complex_product_no_overflow Are Aim Bre Bim (z ∘ data)
    (section5_complex_entry_index n i)
  exact section5_twos_complement_decode_mod (2*n+a+b) (z' ∘ p i) _ (hval i)
    (abs_lt.mp hbnd).1.le (abs_lt.mp hbnd).2
