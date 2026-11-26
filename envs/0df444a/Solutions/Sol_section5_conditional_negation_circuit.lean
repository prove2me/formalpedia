-- Prove2me | solution 1 for section5_conditional_negation_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:01.281164+00:00
-- url     : https://prove2.me/submissions/68ed7561-c64c-4af6-8112-8a6bf4715cfc

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5ConditionalNegation
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_bitsToNatLSB_add_two_pow_rev
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlConstXorCircuit_implements
import Theorems.Thm_section5_controlled_add_update
import Theorems.Thm_section5_embed_reversible_clean_permutation
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

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router






















lemma bitsToNatLSB_all_false (w : ℕ) : bitsToNatLSB (fun _ : Fin w => false) = 0 := by
  simp [bitsToNatLSB]





/-! ### Part 2: Zero-Ancilla Register Primitives -/
































































private lemma ctrlConstPrefixCircuit_size (w c k : ℕ) (hk : k ≤ w) :
    (ctrlConstPrefixCircuit w c k hk).size ≤ k := by
  induction k with
  | zero => simp [ctrlConstPrefixCircuit]
  | succ k ih =>
    dsimp only [ctrlConstPrefixCircuit]
    split_ifs <;> have h := ih (by omega) <;> simp <;> omega





lemma ctrlConstXorCircuit_size (w c : ℕ) : (ctrlConstXorCircuit w c).size ≤ w :=
  ctrlConstPrefixCircuit_size w c w le_rfl





/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/





@[simp] private lemma cuccaroMAJ_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroMAJ c b a hcb hca hba).size = 7 := by
  simp [cuccaroMAJ]

@[simp] private lemma cuccaroUMA_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroUMA c b a hcb hca hba).size = 7 := by
  simp [cuccaroUMA]















lemma cuccaroCore_size (w : ℕ) : (cuccaroCore w).size = 14 * w := by
  induction w with
  | zero => simp [cuccaroCore]
  | succ w ih =>
    simp only [cuccaroCore, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      cuccaroMAJ_size, cuccaroUMA_size, ih]
    omega









lemma addInPlaceCircuit_size (w : ℕ) : (addInPlaceCircuit w).size = 14 * w := by
  simp [addInPlaceCircuit, cuccaroCore_size]















































/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/



































































lemma ctrlAddConstInPlaceCircuit_size (w c : ℕ) : (ctrlAddConstInPlaceCircuit w c).size ≤ 16 * w := by
  dsimp only [ctrlAddConstInPlaceCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, addInPlaceCircuit_size]
  have h1 := ctrlConstXorCircuit_size w c
  omega















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

/-! Actual NOT/CNOT/Toffoli implementations of the accepted linear-size adders. -/

theorem section5_rev_cuccaro_maj {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) :
    section5_RevRealizable (Aux_w54_arith.cuccaroMAJ c b a hcb hca hba) := by
  exact section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
    (section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
      (section5_rev_realizable_toffoli _ _ _ _ _ _))

theorem section5_rev_cuccaro_uma {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) :
    section5_RevRealizable (Aux_w54_arith.cuccaroUMA c b a hcb hca hba) := by
  exact section5_rev_realizable_seq (section5_rev_realizable_toffoli _ _ _ _ _ _)
    (section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
      (section5_rev_realizable_cnot _ _ _))

theorem section5_rev_cuccaro_core (w : ℕ) : section5_RevRealizable (Aux_w54_arith.cuccaroCore w) := by
  induction w with
  | zero => exact section5_rev_realizable_id 1
  | succ w ih =>
    dsimp only [Aux_w54_arith.cuccaroCore]
    exact section5_rev_realizable_seq (section5_rev_cuccaro_maj _ _ _ _ _ _)
      (section5_rev_realizable_seq (section5_rev_realizable_map_wires _ ih)
        (section5_rev_cuccaro_uma _ _ _ _ _ _))

theorem section5_rev_adder (w : ℕ) : section5_RevRealizable (Aux_w54_arith.addInPlaceCircuit w) :=
  section5_rev_realizable_map_wires _ (section5_rev_cuccaro_core w)



theorem section5_rev_ctrl_constant_prefix (w c k : ℕ) (hk : k ≤ w) :
    section5_RevRealizable (Aux_w54_arith.ctrlConstPrefixCircuit w c k hk) := by
  induction k with
  | zero => exact section5_rev_realizable_id _
  | succ k ih =>
    dsimp only [Aux_w54_arith.ctrlConstPrefixCircuit]
    split_ifs
    · exact section5_rev_realizable_seq (ih _) (section5_rev_realizable_cnot _ _ _)
    · exact ih _

theorem section5_rev_ctrl_constant_xor (w c : ℕ) :
    section5_RevRealizable (Aux_w54_arith.ctrlConstXorCircuit w c) :=
  section5_rev_ctrl_constant_prefix w c w le_rfl

theorem section5_rev_ctrl_constant_add (w c : ℕ) :
    section5_RevRealizable (Aux_w54_arith.ctrlAddConstInPlaceCircuit w c) := by
  exact section5_rev_realizable_seq
    (section5_rev_realizable_map_wires _ (section5_rev_ctrl_constant_xor w c))
    (section5_rev_realizable_seq (section5_rev_realizable_map_wires _ (section5_rev_adder w))
      (section5_rev_realizable_map_wires _ (section5_rev_ctrl_constant_xor w c)))









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Actual linear-size conditional two's-complement negation. The control and all
other registers are preserved, and the adder's workspace is returned to zero. -/

theorem section5_control_payload_update {m w : ℕ} (ctrl : Fin m)
    (p : Fin w ↪ Fin m) (hc : ∀ i, ctrl ≠ p i) (z : Qubits m)
    (y : Qubits (1+w)) (v : Qubits w)
    (hy0 : y 0=z ctrl) (hyi : ∀ i, y (Fin.natAdd 1 i)=v i) :
    updateOn (section5_control_payload_embedding ctrl p hc) z y=updateOn p z v := by
  classical
  let e := section5_control_payload_embedding ctrl p hc
  have he0 : e 0=ctrl := rfl
  have hei (i : Fin w) : e (Fin.natAdd 1 i)=p i := combineEmb_natAdd _ _ _ i
  funext j
  by_cases hj : j ∈ Set.range p
  · obtain ⟨i,rfl⟩ := hj
    rw [updateOn_apply_emb]
    change updateOn e z y (p i)=v i
    rw [← hei,updateOn_apply_emb,hyi]
  · rw [updateOn_apply_not_mem p z v hj]
    by_cases hjc : j=ctrl
    · subst j
      change updateOn e z y ctrl=z ctrl
      rw [← he0,updateOn_apply_emb,hy0,he0]
    · apply updateOn_apply_not_mem
      rintro ⟨i,hi⟩
      induction i using Fin.addCases with
      | left i => fin_cases i; exact hjc (hi.symm.trans he0)
      | right i => exact hj ⟨i,(hei i).symm.trans hi⟩

theorem section5_all_ones_bits (w : ℕ) :
    natToBitsLSB w (2^w-1)=(fun _ : Fin w => true) := by
  have h := Aux_w54_arith.bitsToNatLSB_add_two_pow_rev w (fun _ => false)
  simp only [Bool.not_false,Aux_w54_arith.bitsToNatLSB_all_false,add_zero] at h
  rw [← h,natToBitsLSB_bitsToNatLSB]

theorem section5_controlled_complement_circuit {m w : ℕ} (ctrl : Fin m)
    (p : Fin w ↪ Fin m) (hc : ∀ i, ctrl ≠ p i) :
    ∃ c : Circuit gatesRev m, c.size ≤ w ∧
      ∀ z : Qubits m, act c.unitary (ket z)=
        ket (if z ctrl then updateOn p z (fun i => !(z (p i))) else z) := by
  let e := section5_control_payload_embedding ctrl p hc
  let empty : Fin 0 ↪ Fin m := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  obtain ⟨c,hsize,hact⟩ := section5_embed_reversible_clean_permutation
    (Aux_w54_arith.ctrlConstXorCircuit w (2^w-1))
    (Aux_w54_arith.ctrlConstXorFn w (2^w-1))
    (section5_rev_ctrl_constant_xor w (2^w-1))
    (Aux_w54_arith.ctrlConstXorCircuit_implements w (2^w-1))
    e empty (fun _ j => Fin.elim0 j)
  refine ⟨c,hsize.trans (Aux_w54_arith.ctrlConstXorCircuit_size w _),?_⟩
  intro z
  rw [hact z (fun j => Fin.elim0 j)]
  have he0 : e 0=ctrl := rfl
  have hei (i : Fin w) : e (Fin.natAdd 1 i)=p i := combineEmb_natAdd _ _ _ i
  by_cases hz : z ctrl=true
  · rw [if_pos hz]
    congr 1
    apply section5_control_payload_update ctrl p hc z _ _
    · simp [Aux_w54_arith.ctrlConstXorFn,Function.comp_apply,he0,hz]
    · intro i
      simp only [Aux_w54_arith.ctrlConstXorFn,Function.comp_apply,he0,hz,↓reduceIte,
        Fin.val_natAdd,Nat.le_add_right,↓reduceDIte,Nat.add_sub_cancel_left]
      rw [show (⟨i.val,by omega⟩ : Fin w)=i from Fin.ext rfl,section5_all_ones_bits,hei]
      simpa only [show e ⟨0,by omega⟩=ctrl from rfl,hz,↓reduceIte] using
        Bool.xor_true (z (p i))
  · rw [if_neg hz]
    have hsame : Aux_w54_arith.ctrlConstXorFn w (2^w-1) (z ∘ e)=z ∘ e := by
      funext i
      simp [Aux_w54_arith.ctrlConstXorFn,Function.comp_apply,he0,hz]
    rw [hsame]
    congr 1
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hi
      exact updateOn_apply_emb e z (z ∘ e) j
    · exact updateOn_apply_not_mem e z (z ∘ e) hi





end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Embedding clean reversible arithmetic in an arbitrary postprocessing register. -/



theorem section5_embedded_classical_controlled_add {m : ℕ} (w a : ℕ)
    (eMain : Fin (1+w) ↪ Fin m) (eAnc : Fin (w+1) ↪ Fin m)
    (hdisj : ∀ i j, eMain i ≠ eAnc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w ∧
      ∀ z : Qubits m, (∀ j, z (eAnc j)=false) →
        act c.unitary (ket z)=
          ket (updateOn eMain z (Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ eMain))) := by
  obtain ⟨c,hc,hact⟩ := section5_embed_reversible_clean_permutation
    (Aux_w54_arith.ctrlAddConstInPlaceCircuit w a) (Aux_w54_arith.ctrlAddConstInPlaceFn w a)
    (section5_rev_ctrl_constant_add w a) (Aux_w54_arith.ctrlAddConstInPlaceCircuit_implements w a)
    eMain eAnc hdisj
  exact ⟨c,hc.trans (Aux_w54_arith.ctrlAddConstInPlaceCircuit_size w a),hact⟩







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m w : ℕ} (hw : 0 < w) (ctrl : Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hcp : ∀ i, ctrl ≠ p i) (hca : ∀ j, ctrl ≠ anc j)
    (hpa : ∀ i j, p i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 17*w ∧
      ∀ z : Qubits m, (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_conditional_negate ctrl p z) := by
  classical
  obtain ⟨c,hc,hact⟩ := section5_controlled_complement_circuit ctrl p hcp
  let e := section5_control_payload_embedding ctrl p hcp
  have he0 : e 0=ctrl := rfl
  have hei (i : Fin w) : e (Fin.natAdd 1 i)=p i := combineEmb_natAdd _ _ _ i
  have hea : ∀ i j, e i ≠ anc j := by
    intro i j
    induction i using Fin.addCases with
    | left i => fin_cases i; exact hca j
    | right i => rw [hei]; exact hpa i j
  obtain ⟨d,hd,hdact⟩ := section5_embedded_classical_controlled_add w 1 e anc hea
  refine ⟨c++d,?_,?_⟩
  · simp only [Circuit.size,List.length_append]
    change c.length ≤ _ at hc
    change d.length ≤ _ at hd
    omega
  · intro z hz
    rw [section5_boolean_circuit_append,hact]
    by_cases hzc : z ctrl=true
    · rw [if_pos hzc]
      let z' := updateOn p z (fun i => !(z (p i)))
      have hz'a (j : Fin (w+1)) : z' (anc j)=false := by
        exact (updateOn_apply_not_mem p z _ (by rintro ⟨i,hi⟩; exact hpa i j hi)).trans (hz j)
      have hz'c : z' ctrl=true := by
        exact (updateOn_apply_not_mem p z _ (by rintro ⟨i,hi⟩; exact hcp i hi.symm)).trans hzc
      rw [hdact z' hz'a,section5_controlled_add_update,if_pos hz'c]
      unfold section5_conditional_negate
      rw [if_pos hzc]
      have hones := Aux_w54_arith.bitsToNatLSB_add_two_pow_rev w (z ∘ p)
      have hval : 1%2^w+bitsToNatLSB (z' ∘ p)=2^w-bitsToNatLSB (z ∘ p) := by
        have htwo : 1 < 2^w := Nat.one_lt_two_pow_iff.mpr (by omega)
        rw [Nat.mod_eq_of_lt htwo]
        have hz'p : z' ∘ p=fun i => !(z (p i)) := by
          funext i
          exact updateOn_apply_emb p z (fun i => !(z (p i))) i
        rw [hz'p]
        change bitsToNatLSB (fun i => !(z (p i)))+bitsToNatLSB (z ∘ p)=2^w-1 at hones
        omega
      rw [hval]
      congr 1
      funext i
      by_cases hi : i ∈ Set.range p
      · obtain ⟨j,rfl⟩ := hi
        rw [updateOn_apply_emb,updateOn_apply_emb]
      · rw [updateOn_apply_not_mem p z' _ hi,updateOn_apply_not_mem p z _ hi,
          show z' i=z i from updateOn_apply_not_mem p z _ hi]
    · rw [if_neg hzc,hdact z hz,section5_controlled_add_update,if_neg hzc]
      simp [section5_conditional_negate,hzc]
