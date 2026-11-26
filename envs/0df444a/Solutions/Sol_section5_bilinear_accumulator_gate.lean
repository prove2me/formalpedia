-- Prove2me | solution 1 for section5_bilinear_accumulator_gate
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:36.89502+00:00
-- url     : https://prove2.me/submissions/0cab1636-1d84-435f-99cb-c015ef913823

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
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_section5_boolean_gate_action
import Theorems.Thm_section5_controlled_add_update
import Theorems.Thm_section5_embed_reversible_clean_permutation
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A product of two input bits can control the linear-size modular accumulator.
The temporary AND bit and all arithmetic workspace are returned to zero. -/

theorem section5_updateOn_commute_update {m w : ℕ} (p : Fin w ↪ Fin m)
    (t : Fin m) (ht : t ∉ Set.range p) (z : Qubits m) (x : Qubits w) (b : Bool) :
    updateOn p (Function.update z t b) x=Function.update (updateOn p z x) t b := by
  classical
  funext j
  by_cases hj : j=t
  · subst j
    rw [updateOn_apply_not_mem p _ _ ht,Function.update_self,Function.update_self]
  · by_cases hmem : j ∈ Set.range p
    · obtain ⟨i,rfl⟩ := hmem
      rw [updateOn_apply_emb,Function.update_of_ne hj,updateOn_apply_emb]
    · rw [updateOn_apply_not_mem p _ _ hmem,Function.update_of_ne hj,
        Function.update_of_ne hj,updateOn_apply_not_mem p _ _ hmem]

theorem section5_update_off_register {m w : ℕ} (p : Fin w ↪ Fin m)
    (t : Fin m) (ht : t ∉ Set.range p) (z : Qubits m) (b : Bool) :
    Function.update z t b ∘ p=z ∘ p := by
  classical
  funext i
  exact Function.update_of_ne (fun heq => ht ⟨i,heq⟩) b z



theorem section5_bilinear_step_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (a b : Fin m) (v : ℕ) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_bilinear_step p a b v z j=z j := by
  unfold section5_bilinear_step
  split_ifs
  · exact updateOn_apply_not_mem p z _ hj
  · rfl

















end
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



































theorem section5_boolean_gate_size {m : ℕ} (op : BoolOp) (a b t : Fin m) (hat : a ≠ t) (hbt : b ≠ t) :
    (section5_boolean_gate_circuit op a b t hat hbt).size ≤ 3 := by
  cases op <;> simp [section5_boolean_gate_circuit,Circuit.size] <;> split_ifs <;> simp











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




























/-! ### Part 2: Zero-Ancilla Register Primitives -/







































private lemma cswapPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (cswapPrefixCircuit w k hk).size = 7 * k := by
  induction k with
  | zero => simp [cswapPrefixCircuit]
  | succ k ih => simp [cswapPrefixCircuit, ih (by omega)]; omega





@[simp] lemma cswapRegCircuit_size (w : ℕ) : (cswapRegCircuit w).size = 7 * w :=
  cswapPrefixCircuit_size w w le_rfl


















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











@[simp] private lemma cuccaroShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w)) :
    (cuccaroShiftEmb w i).1 = if i.1 = 0 then 1 else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1))) else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl



lemma cuccaroCore_size (w : ℕ) : (cuccaroCore w).size = 14 * w := by
  induction w with
  | zero => simp [cuccaroCore]
  | succ w ih =>
    simp only [cuccaroCore, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      cuccaroMAJ_size, cuccaroUMA_size, ih]
    omega





@[simp] private lemma cuccaroWireEmb_val (w : ℕ) (u : Fin (1 + 2 * w)) :
    (cuccaroWireEmb w u).1 =
      if u.1 = 0 then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w, _⟩ : Fin ((w + w) + 1))
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl



lemma addInPlaceCircuit_size (w : ℕ) : (addInPlaceCircuit w).size = 14 * w := by
  simp [addInPlaceCircuit, cuccaroCore_size]

















@[simp] private lemma cuccaroCarryShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w + 1)) :
    (cuccaroCarryShiftEmb w i).1 =
      if i.1 = 0 then 1 else if i.1 = 1 + 2 * w then 1 + 2 * (w + 1) else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1) + 1))
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), _⟩ else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl















@[simp] private lemma ltFlipEmb_val (w : ℕ) (i : Fin w) : (ltFlipEmb w i).1 = i.1 := rfl



@[simp] private lemma ltCarryEmb_val (w : ℕ) (u : Fin (1 + 2 * w + 1)) :
    (ltCarryEmb w u).1 =
      if u.1 = 0 then w + w + 1
      else if u.1 = 1 + 2 * w then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w + 1, _⟩ : Fin ((w + w + 1) + 1))
    else if u.1 = 1 + 2 * w then ⟨w + w, _⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl









/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/

















@[simp] private lemma cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (cAddCopyEmb w u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (if u.1 < 1 + w then (⟨u.1, _⟩ : Fin ((1 + w + w) + (w + 1))) else ⟨u.1 + w, _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (cAddCopyEmb w (Fin.castAdd 0 u)).1 = _
  rw [cAddCopyEmb_val]; rfl































@[simp] private lemma cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (cacXorEmb w u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (if u.1 = 0 then (⟨0, _⟩ : Fin ((1 + w) + (w + 1))) else ⟨1 + w + (u.1 - 1), _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (((Fin.castAddEmb 0).trans (cacXorEmb w)) u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (cacXorEmb w (Fin.castAdd 0 u)).1 = _
  rw [cacXorEmb_val]; rfl













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
theorem solution {m w : ℕ}
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t a b : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hat : a ≠ t) (hbt : b ≠ t)
    (hap : a ∉ Set.range p) (hbp : b ∉ Set.range p) (v : ℕ) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w+6 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_bilinear_step p a b v z) := by
  classical
  let d := section5_boolean_gate_circuit BoolOp.and a b t hat hbt
  let e := section5_control_payload_embedding t p (fun i heq => htp ⟨i,heq.symm⟩)
  have hdisj : ∀ i j, e i ≠ anc j := by
    intro i j
    induction i using Fin.addCases with
    | left i => fin_cases i; exact hta j
    | right i =>
      have hei : e (Fin.natAdd 1 i)=p i := combineEmb_natAdd _ _ _ i
      rw [hei]
      exact hpa i j
  obtain ⟨c,hc,hact⟩ := section5_embedded_classical_controlled_add w v e anc hdisj
  refine ⟨d++c++d,?_,?_⟩
  · have hd := section5_boolean_gate_size BoolOp.and a b t hat hbt
    simp only [Circuit.size,List.length_append] at *
    change d.length ≤ 3 at hd
    omega
  · intro z hzt hzanc
    let r := z a && z b
    let z1 := Function.update z t r
    let z2 := section5_bilinear_step p a b v z
    have hd1 : act d.unitary (ket z)=ket z1 := by
      have hh := section5_boolean_gate_action BoolOp.and a b t hat hbt z
      simpa only [section5_bool_value,hzt,Bool.false_xor] using hh
    have hclean1 : ∀ j, z1 (anc j)=false := by
      intro j
      rw [show z1 (anc j)=z (anc j) from Function.update_of_ne (Ne.symm (hta j)) r z,hzanc j]
    have hadd : act c.unitary (ket z1)=ket (Function.update z2 t r) := by
      rw [hact z1 hclean1]
      have heq := section5_controlled_add_update v t p
        (fun i heq => htp ⟨i,heq.symm⟩) z1
      change updateOn e z1 _ = _ at heq
      rw [heq]
      congr 1
      have hz1t : z1 t=r := Function.update_self t r z
      have hz1p : z1 ∘ p=z ∘ p := section5_update_off_register p t htp z r
      rw [hz1t,hz1p]
      dsimp only [z2,section5_bilinear_step]
      change (if r then updateOn p (Function.update z t r)
          (natToBitsLSB w (v%2^w+bitsToNatLSB (z ∘ p))) else Function.update z t r)=
        Function.update (if r then updateOn p z
          (natToBitsLSB w (v%2^w+bitsToNatLSB (z ∘ p))) else z) t r
      by_cases hr : r
      · simp only [hr,↓reduceIte]
        exact section5_updateOn_commute_update p t htp z _ true
      · simp only [hr,Bool.false_eq_true,↓reduceIte]
    have hz2t : z2 t=false := (section5_bilinear_step_off p a b v z t htp).trans hzt
    have hz2a : z2 a=z a := section5_bilinear_step_off p a b v z a hap
    have hz2b : z2 b=z b := section5_bilinear_step_off p a b v z b hbp
    have hd2 : act d.unitary (ket (Function.update z2 t r))=ket z2 := by
      have hh := section5_boolean_gate_action BoolOp.and a b t hat hbt (Function.update z2 t r)
      simpa only [Function.update_self,Function.update_of_ne hat,Function.update_of_ne hbt,
        hz2a,hz2b,section5_bool_value,← show (z a && z b)=r from rfl,Bool.xor_self,
        Function.update_idem,← hz2t,Function.update_eq_self] using hh
    rw [section5_boolean_circuit_append,section5_boolean_circuit_append,hd1,hadd,hd2]
