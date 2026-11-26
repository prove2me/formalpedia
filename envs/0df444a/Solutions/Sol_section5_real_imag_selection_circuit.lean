-- Prove2me | solution 1 for section5_real_imag_selection_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:17.339264+00:00
-- url     : https://prove2.me/submissions/42a6e105-e95c-49b3-8204-2a6d410bba02

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
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5RealImagSelection
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
import Theorems.Thm_section5_embed_reversible_clean_permutation
import Theorems.Thm_section5_general_signed_dot_circuit
import Theorems.Thm_section5_record_swap_value_A
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_twos_complement_decode_mod
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/















theorem section5_toffoli_matrix_action (y z : Qubits 3) :
    section5_toffoli_gate.mat y z=if y=section5_toffoli_perm z then 1 else 0 := by
  have heq : y=section5_toffoli_perm z ↔ y 0=z 0 ∧ y 1=z 1 ∧ y 2=xor (z 2) (z 0 && z 1) := by
    constructor
    · intro h; exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
    · intro h; funext i; fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  change (if y 0=z 0 ∧ y 1=z 1 ∧ y 2=xor (z 2) (z 0 && z 1) then (1:ℂ) else 0)=_
  simp only [heq]















































theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Reusing the accepted arithmetic circuits in the actual classical postprocessing gate set. -/





theorem section5_rev_map_wires_size {m n : ℕ} (e : Fin m ↪ Fin n) (c : Circuit gatesRev m) :
    (section5_rev_map_wires e c).size=c.size := by simp [section5_rev_map_wires,Circuit.size]

theorem section5_rev_map_wires_unitary {m n : ℕ} (e : Fin m ↪ Fin n) (c : Circuit gatesRev m) :
    (section5_rev_map_wires e c).unitary=embedOp c.unitary e := by
  induction c with
  | nil => simp [section5_rev_map_wires,Circuit.unitary,embedOp_one]
  | cons g c ih =>
    simp only [section5_rev_map_wires,List.map_cons,circuit_unitary_cons] at ih ⊢
    rw [ih,embedOp_mul,embedOp_embedOp]

theorem section5_rev_realizable_id (m : ℕ) : section5_RevRealizable (LayeredCircuit.id m) := by
  refine ⟨[],by simp [Circuit.size],?_⟩
  simp [Circuit.unitary]

theorem section5_rev_realizable_seq {m : ℕ} {a b : LayeredCircuit m}
    (ha : section5_RevRealizable a) (hb : section5_RevRealizable b) :
    section5_RevRealizable (a.seq b) := by
  obtain ⟨c,hc,hcu⟩ := ha
  obtain ⟨d,hd,hdu⟩ := hb
  refine ⟨c++d,?_,?_⟩
  · simpa only [Circuit.size,List.length_append,LayeredCircuit.seq_size] using add_le_add hc hd
  · rw [circuit_unitary_append,hcu,hdu,LayeredCircuit.seq_unitary]

theorem section5_rev_realizable_map_wires {m n : ℕ} (e : Fin m ↪ Fin n) {lc : LayeredCircuit m}
    (h : section5_RevRealizable lc) : section5_RevRealizable (lc.mapWires e) := by
  obtain ⟨c,hc,hcu⟩ := h
  refine ⟨section5_rev_map_wires e c,?_,?_⟩
  · simpa only [section5_rev_map_wires_size,LayeredCircuit.mapWires_size] using hc
  · rw [section5_rev_map_wires_unitary,hcu,LayeredCircuit.mapWires_unitary]



theorem section5_rev_realizable_cnot {m : ℕ} (a t : Fin m) (hat : a ≠ t) :
    section5_RevRealizable (cnotGate a t hat) := by
  refine ⟨[section5_rev_cnot (wire2Emb a t hat)],by norm_num [Circuit.size,cnotGate],?_⟩
  simp only [cnotGate,LayeredCircuit.single_unitary,cnotApp,gate2App]
  simp [Circuit.unitary,section5_rev_cnot]

theorem section5_rev_realizable_toffoli3 : section5_RevRealizable toffoli3 := by
  refine ⟨[section5_rev_toffoli (Function.Embedding.refl _)],by norm_num [Circuit.size],?_⟩
  rw [toffoli3_unitary]
  have hmat : section5_toffoli_gate.mat=toffoliMat := by
    ext y z
    exact section5_toffoli_matrix_action y z
  have hfull {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) :
      embedOp M (Function.Embedding.refl _)=M := by
    ext y z
    simp [embedOp,Function.comp_def]
  simp only [Circuit.unitary,section5_rev_toffoli,List.map_cons,List.map_nil,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.prod_cons,List.prod_nil,mul_one]
  exact (hfull (k := 3) section5_toffoli_gate.mat).trans hmat

theorem section5_rev_realizable_toffoli {m : ℕ} (a b t : Fin m)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    section5_RevRealizable (toffoliOn a b t hab hat hbt) :=
  section5_rev_realizable_map_wires _ section5_rev_realizable_toffoli3









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Comparing a score subregister and conditionally exchanging its complete record.
This is the reversible step in the maximum-column scan. -/

























theorem section5_combineEmb_range {m a b : ℕ} (A : Fin a ↪ Fin m) (B : Fin b ↪ Fin m)
    (hAB : ∀ i j, A i ≠ B j) {j : Fin m} (hj : j ∈ Set.range (combineEmb A B hAB)) :
    j ∈ Set.range A ∨ j ∈ Set.range B := by
  obtain ⟨i,rfl⟩ := hj
  induction i using Fin.addCases with
  | left i => exact Or.inl ⟨i,(combineEmb_castAdd A B hAB i).symm⟩
  | right i => exact Or.inr ⟨i,(combineEmb_natAdd A B hAB i).symm⟩



theorem section5_record_swap_off_range {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (j : Fin m) (hjA : j ∉ Set.range A) (hjB : j ∉ Set.range B) (hjc : j ≠ ctrl) :
    j ∉ Set.range (section5_record_swap_wires A B ctrl hAB hcA hcB) := by
  intro hj
  have hor := section5_combineEmb_range
    (combineEmb (section5_boolean_wire1 ctrl) A (fun _ i => hcA i)) B _ hj
  rcases hor with hfirst | hB
  · have hs := section5_combineEmb_range (section5_boolean_wire1 ctrl) A _ hfirst
    rcases hs with ⟨i,hi⟩ | hA
    · exact hjc hi.symm
    · exact hjA hA
  · exact hjB hB



end
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router




























/-! ### Part 2: Zero-Ancilla Register Primitives -/







































private lemma cswapPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (cswapPrefixCircuit w k hk).size = 7 * k := by
  induction k with
  | zero => simp [cswapPrefixCircuit]
  | succ k ih => simp [cswapPrefixCircuit, ih (by omega)]; omega





@[simp] lemma cswapRegCircuit_size (w : ℕ) : (cswapRegCircuit w).size = 7 * w :=
  cswapPrefixCircuit_size w w le_rfl






























/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

















































































/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/



















































































/-! ### MSB-First Circuit Wrappers via Zero-Gate `Fin.revPerm` Conjugation -/













-- 1. setConstMSBCircuit






-- 2. ctrlConstXorMSBCircuit






-- 3. eqConstMSBCircuit






-- 4. ltConstMSBCircuit






-- 5. ltRegMSBCircuit






-- 6 & 7. addInPlaceMSBCircuit & subInPlaceMSBCircuit
















-- 8 & 9. ctrlAddInPlaceMSBCircuit & ctrlSubInPlaceMSBCircuit
















-- 10 & 11. ctrlAddConstInPlaceMSBCircuit & ctrlSubConstInPlaceMSBCircuit












end Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_arith




end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Reversible conditional register selection for the maximum-column decoder. -/

theorem section5_rev_controlled_swap3 : section5_RevRealizable cswap3 := by
  exact section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
    (section5_rev_realizable_seq (section5_rev_realizable_toffoli _ _ _ _ _ _)
      (section5_rev_realizable_cnot _ _ _))

theorem section5_rev_controlled_swap {m : ℕ} (ctrl a b : Fin m)
    (hca : ctrl ≠ a) (hcb : ctrl ≠ b) (hab : a ≠ b) :
    section5_RevRealizable (cswapOn ctrl a b hca hcb hab) :=
  section5_rev_realizable_map_wires _ section5_rev_controlled_swap3

theorem section5_rev_controlled_swap_prefix (w k : ℕ) (hk : k ≤ w) :
    section5_RevRealizable (Aux_w54_arith.cswapPrefixCircuit w k hk) := by
  induction k with
  | zero => exact section5_rev_realizable_id _
  | succ k ih =>
    dsimp only [Aux_w54_arith.cswapPrefixCircuit]
    exact section5_rev_realizable_seq (ih (by omega))
      (section5_rev_controlled_swap _ _ _ _ _ _)

theorem section5_rev_controlled_swap_register (w : ℕ) :
    section5_RevRealizable (Aux_w54_arith.cswapRegCircuit w) :=
  section5_rev_controlled_swap_prefix w w le_rfl



theorem section5_embedded_controlled_swap_register {m : ℕ} (w : ℕ)
    (emain : Fin (1+w+w) ↪ Fin m) :
    ∃ c : Circuit gatesRev m, c.size ≤ 7*w ∧
      ∀ z : Qubits m, act c.unitary (ket z)=
        ket (updateOn emain z (cswapRegFn w (z ∘ emain))) := by
  let empty : Fin 0 ↪ Fin m := ⟨Fin.elim0,fun j => Fin.elim0 j⟩
  obtain ⟨c,hc,hact⟩ := section5_embed_reversible_clean_permutation
    (Aux_w54_arith.cswapRegCircuit w) (cswapRegFn w)
    (section5_rev_controlled_swap_register w) (Aux_w54_arith.cswapRegCircuit_implements w)
    emain empty (fun _ j => Fin.elim0 j)
  exact ⟨c,hc.trans (Aux_w54_arith.cswapRegCircuit_size w).le,fun z => hact z (fun j => Fin.elim0 j)⟩

end
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

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Select the larger real/imaginary vector without square roots. A signed
sum-of-squares difference controls an actual reversible register swap. -/







theorem section5_real_imag_difference {m n b : ℕ} (A B : Fin (n*(b+1)) ↪ Fin m)
    (z : Qubits m) :
    (∑ i : Fin (n+n),
      section5_integer_bit_value (section5_real_imag_coefficients n b i)
        (z ∘ section5_real_imag_wires A B i)*
      section5_integer_bit_value (section5_twos_coefficient (b+1))
        (z ∘ section5_real_imag_wires A B i))=
      section5_signed_vector_square A z-section5_signed_vector_square B z := by
  rw [Fin.sum_univ_add]
  simp only [section5_real_imag_coefficients,section5_real_imag_wires,
    Fin.addCases_left,Fin.addCases_right,section5_integer_bit_value_neg,
    neg_mul,Finset.sum_neg_distrib,section5_signed_vector_square,pow_two,Function.comp_def]
  ring

theorem section5_real_imag_difference_bound {m n b : ℕ} (A B : Fin (n*(b+1)) ↪ Fin m)
    (z : Qubits m) :
    |section5_signed_vector_square A z-section5_signed_vector_square B z| <
      (2:ℤ)^(n+b+b+1) := by
  have ha := section5_signed_dot_no_overflow
    (fun i : Fin n => fun e => z (A (finProdFinEquiv (i,e))))
    (fun i : Fin n => fun e => z (A (finProdFinEquiv (i,e))))
  have hb := section5_signed_dot_no_overflow
    (fun i : Fin n => fun e => z (B (finProdFinEquiv (i,e))))
    (fun i : Fin n => fun e => z (B (finProdFinEquiv (i,e))))
  have ha' : |section5_signed_vector_square A z| < (2:ℤ)^(n+b+b) := by
    simpa only [section5_signed_vector_square,pow_two] using ha
  have hb' : |section5_signed_vector_square B z| < (2:ℤ)^(n+b+b) := by
    simpa only [section5_signed_vector_square,pow_two] using hb
  have hh := abs_sub (section5_signed_vector_square A z) (section5_signed_vector_square B z)
  rw [pow_succ]
  omega



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



theorem section5_integer_dot_sign_bit (b : ℕ) (z : Qubits (b+1)) (v : ℤ)
    (hmod : (bitsToNatLSB z : ZMod (2^(b+1)))=(v : ZMod (2^(b+1))))
    (hlo : -(2:ℤ)^b ≤ v) (hhi : v < (2:ℤ)^b) :
    0 ≤ v ↔ z (Fin.last b)=false := by
  rw [← section5_twos_complement_decode_mod b z v hmod hlo hhi]
  exact section5_twos_complement_nonnegative b z

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m n b : ℕ}
    (A B : Fin (n*(b+1)) ↪ Fin m)
    (p : Fin (n+b+b+1+1) ↪ Fin m) (anc : Fin (n+b+b+1+1+1) ↪ Fin m)
    (t : Fin m) (hAB : ∀ i j, A i ≠ B j)
    (hpa : ∀ i j, p i ≠ anc j) (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i, A i ≠ t) (hBt : ∀ i, B i ≠ t)
    (hAp : ∀ i, A i ∉ Set.range p) (hBp : ∀ i, B i ∉ Set.range p) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (16*(n+b+b+1+1)+6)*((n+n)*(b+1)*(b+1))+7*(n*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ e, z (p e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (z' ∘ A=if section5_signed_vector_square A z < section5_signed_vector_square B z
            then z ∘ B else z ∘ A) ∧
          ∀ j, j ∉ Set.range A → j ∉ Set.range B → j ∉ Set.range p → z' j=z j := by
  classical
  have hwires_t : ∀ i e, section5_real_imag_wires A B i e ≠ t := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [section5_real_imag_wires,Fin.addCases_left] using fun e => hAt (finProdFinEquiv (j,e))
    · simpa only [section5_real_imag_wires,Fin.addCases_right] using fun e => hBt (finProdFinEquiv (j,e))
  have hwires_p : ∀ i e, section5_real_imag_wires A B i e ∉ Set.range p := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [section5_real_imag_wires,Fin.addCases_left] using fun e => hAp (finProdFinEquiv (j,e))
    · simpa only [section5_real_imag_wires,Fin.addCases_right] using fun e => hBp (finProdFinEquiv (j,e))
  obtain ⟨cd,hd,hda⟩ := section5_general_signed_dot_circuit
    (section5_real_imag_coefficients n b) (fun _ => section5_twos_coefficient (b+1))
    (section5_real_imag_wires A B) (section5_real_imag_wires A B) p anc hpa t htp hta
    hwires_t hwires_t hwires_p hwires_p
  let ctrl := p (Fin.last (n+b+b+1))
  have hcA : ∀ i, ctrl ≠ A i := by intro i h; exact hAp i ⟨_,h⟩
  have hcB : ∀ i, ctrl ≠ B i := by intro i h; exact hBp i ⟨_,h⟩
  let sw := section5_record_swap_wires A B ctrl hAB hcA hcB
  obtain ⟨cs,hs,hsa⟩ := section5_embedded_controlled_swap_register (n*(b+1)) sw
  refine ⟨cd++cs,?_,?_⟩
  · simpa only [Circuit.size,List.length_append] using add_le_add hd hs
  · intro z hzt hza hz0
    obtain ⟨z1,hz1,hoff,hmod⟩ := hda z hzt hza
    have hzero : bitsToNatLSB (z ∘ p)=0 := by simp [bitsToNatLSB,hz0]
    rw [hzero,Nat.cast_zero,zero_add,section5_real_imag_difference] at hmod
    have hbnd := section5_real_imag_difference_bound A B z
    have hsign := section5_integer_dot_sign_bit (n+b+b+1) (z1 ∘ p) _ hmod
      (abs_lt.mp hbnd).1.le (abs_lt.mp hbnd).2
    have hA1 : z1 ∘ A=z ∘ A := by funext i; exact hoff _ (hAp i)
    have hB1 : z1 ∘ B=z ∘ B := by funext i; exact hoff _ (hBp i)
    let z2 := updateOn sw z1 (QuantumLTF.Membership.Supplement.LcgSym54.cswapRegFn (n*(b+1)) (z1 ∘ sw))
    refine ⟨z2,?_,?_,?_⟩
    · rw [section5_boolean_circuit_append,hz1]
      exact hsa z1
    · have hh := section5_record_swap_value_A A B ctrl hAB hcA hcB z1
      change z2 ∘ A=if z1 ctrl then z1 ∘ B else z1 ∘ A at hh
      rw [hh,hA1,hB1]
      by_cases h : 0 ≤ section5_signed_vector_square A z-section5_signed_vector_square B z
      · have hc : z1 ctrl=false := hsign.mp h
        simp only [hc,Bool.false_eq_true,↓reduceIte,not_lt_of_ge (sub_nonneg.mp h)]
      · have hc : z1 ctrl=true := Bool.eq_true_of_not_eq_false (fun hc => h (hsign.mpr hc))
        simp only [hc,↓reduceIte,show section5_signed_vector_square A z <
          section5_signed_vector_square B z from by omega]
    · intro j hjA hjB hjp
      exact (updateOn_apply_not_mem sw z1 _
        (section5_record_swap_off_range A B ctrl hAB hcA hcB j hjA hjB
          (fun h => hjp ⟨_,h.symm⟩))).trans (hoff j hjp)
