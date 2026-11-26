-- Prove2me | solution 1 for section5_column_scores_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:14.958226+00:00
-- url     : https://prove2.me/submissions/f81bcd0d-8f0e-4789-9428-7a7fdded6b0d

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
import Definitions.Def_Section5Verified_Section5ColumnScoreCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_batched_bilinear_circuit
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_twos_complement_decode_mod
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact squared column norms, computed into unsigned registers before the
maximum-record scan. The matrix input and shared arithmetic workspace are preserved. -/





theorem section5_column_square_expansion {r n b : ℕ}
    (re im : Fin n → Fin n → Fin (b+1) → Fin r) (j : Fin n) (z : Qubits r) :
    (∑ i : Fin (n+n),
      section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ section5_column_score_wires re im j i)*
      section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ section5_column_score_wires re im j i))=
        section5_complex_column_square re im j z := by
  rw [Fin.sum_univ_add]
  simp only [section5_column_score_wires,Fin.addCases_left,Fin.addCases_right,
    section5_complex_column_square,Finset.sum_add_distrib,pow_two]

theorem section5_column_square_range {r n b : ℕ}
    (re im : Fin n → Fin n → Fin (b+1) → Fin r) (j : Fin n) (z : Qubits r) :
    0 ≤ section5_complex_column_square re im j z ∧
      section5_complex_column_square re im j z < (2:ℤ)^(2*n+b+b) := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · have hh := section5_signed_dot_no_overflow
      (fun i : Fin (n+n) => z ∘ section5_column_score_wires re im j i)
      (fun i : Fin (n+n) => z ∘ section5_column_score_wires re im j i)
    rw [section5_column_square_expansion] at hh
    simpa only [two_mul] using (abs_lt.mp hh).2



end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! The bounded-window integer decoder is exactly the standard signed binary
linear form. This connects the window analysis to the signed dot-product circuit. -/



theorem section5_twos_complement_value (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      (bitsToNatLSB z : ℤ)-(if z (Fin.last b) then (2:ℤ)^(b+1) else 0) := by
  unfold section5_integer_bit_value section5_twos_coefficient bitsToNatLSB
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.add_left_inj,↓reduceIte]
  push_cast
  have hi (i : Fin b) : i.val ≠ b := by omega
  simp_rw [if_neg (hi _)]
  cases hz : z (Fin.last b) <;> simp [hz,pow_succ] <;> ring





theorem section5_twos_complement_nonnegative (b : ℕ) (z : Qubits (b+1)) :
    0 ≤ section5_integer_bit_value (section5_twos_coefficient (b+1)) z ↔
      z (Fin.last b)=false := by
  rw [section5_twos_complement_value]
  have hN : (bitsToNatLSB z:ℤ) < (2:ℤ)^(b+1) := by
    exact_mod_cast bitsToNatLSB_lt (b+1) z
  cases hz : z (Fin.last b) <;> simp [hz] <;> omega





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m r n b : ℕ} (data : Fin r → Fin m)
    (re im : Fin n → Fin n → Fin (b+1) → Fin r)
    (p : Fin n → Fin (2*n+b+b+1) ↪ Fin m)
    (anc : Fin (2*n+b+b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ ((16*(2*n+b+b+1)+6)*((n+n)*(b+1)*(b+1)))*n ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ℤ)=section5_complex_column_square re im i (z ∘ data) := by
  obtain ⟨c,hc,hact⟩ := section5_batched_bilinear_circuit data
    (section5_column_score_wires re im) (section5_column_score_wires re im)
    (fun _ _ => section5_twos_coefficient (b+1)) (fun _ _ => section5_twos_coefficient (b+1))
    p anc t hpair hdata hpa htp hta hdt
  refine ⟨c,hc,?_⟩
  intro z hzt hza hz0
  obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hza hz0
  refine ⟨z',hz',hoff,?_⟩
  intro i
  have he := section5_column_square_expansion re im i (z ∘ data)
  have hmod := (hval i).trans (congrArg (fun v : ℤ => (v:ZMod (2^(2*n+b+b+1)))) he)
  have hbnd := section5_column_square_range re im i (z ∘ data)
  have hdecoded := section5_twos_complement_decode_mod (2*n+b+b) (z' ∘ p i) _ hmod
    ((neg_nonpos.mpr (by positivity : (0:ℤ) ≤ 2^(2*n+b+b))).trans hbnd.1) hbnd.2
  have htop := (section5_twos_complement_nonnegative (2*n+b+b) (z' ∘ p i)).mp
    (by rw [hdecoded]; exact hbnd.1)
  rw [section5_twos_complement_value,htop] at hdecoded
  simpa only [Bool.false_eq_true,↓reduceIte,sub_zero] using hdecoded
