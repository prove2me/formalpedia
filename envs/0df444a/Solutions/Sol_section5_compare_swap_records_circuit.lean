-- Prove2me | solution 1 for section5_compare_swap_records_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:02.583774+00:00
-- url     : https://prove2.me/submissions/ca16418c-9abc-4543-ba24-80af6b522c0d

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
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
import Theorems.Thm_Aux_w54_arith_ltRegCircuit_implements
import Theorems.Thm_section5_embed_reversible_clean_permutation
import Theorems.Thm_section5_record_swap_value_A
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/









theorem section5_not_matrix_action (y z : Qubits 1) :
    (Gate.ofMatrix1 pauliX).mat y z=if y=section5_bit_flip z then 1 else 0 := by
  have heq : y=section5_bit_flip z ↔ y 0=!(z 0) := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h
  change (if y 0=z 0 then (0:ℂ) else 1)=_
  simp only [heq]
  cases hy : y 0 <;> cases hz : z 0 <;> simp [hy,hz]

theorem section5_cnot_matrix_action (y z : Qubits 2) :
    (Gate.ofMatrix2 cnot).mat y z=if y=section5_cnot_perm z then 1 else 0 := by
  have heq : y=section5_cnot_perm z ↔ y 0=z 0 ∧ y 1=xor (z 1) (z 0) := by
    constructor
    · intro h; exact ⟨congrFun h 0,congrFun h 1⟩
    · intro h; funext i; fin_cases i
      · exact h.1
      · exact h.2
  change (if y 0=z 0 ∧ y 1=xor (z 1) (z 0) then (1:ℂ) else 0)=_
  simp only [heq]



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

theorem section5_rev_realizable_not {m : ℕ} (t : Fin m) : section5_RevRealizable (pauliXGate t) := by
  refine ⟨[section5_rev_not (wire1Emb t)],by norm_num [Circuit.size,pauliXGate],?_⟩
  simp only [pauliXGate,LayeredCircuit.single_unitary,pauliXApp,gate1App]
  simp [Circuit.unitary,section5_rev_not]

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

theorem section5_classical_involution_star {k : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (f : Qubits k → Qubits k)
    (hM : ∀ y z, M y z=if y=f z then 1 else 0) (hf : ∀ x, f (f x)=x) : star M=M := by
  classical
  ext y z
  rw [Matrix.star_apply,hM,hM]
  have heq : z=f y ↔ y=f z := by
    constructor <;> intro h
    · rw [h,hf]
    · rw [h,hf]
  simp only [heq]
  split_ifs <;> simp

theorem section5_gatesRev_star_self (g : Gate) (hg : g ∈ gatesRev) : star g.mat=g.mat := by
  simp only [gatesRev,Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact section5_classical_involution_star _ _ section5_not_matrix_action (by intro x; ext i; fin_cases i; simp [section5_bit_flip])
  · exact section5_classical_involution_star _ _ section5_cnot_matrix_action (by intro x; ext i; fin_cases i <;> simp [section5_cnot_perm])
  · exact section5_classical_involution_star _ _ section5_toffoli_matrix_action (by intro x; ext i; fin_cases i <;> simp [section5_toffoli_perm])

theorem section5_rev_reverse_unitary {m : ℕ} (c : Circuit gatesRev m) :
    Circuit.unitary c.reverse=star c.unitary := by
  induction c with
  | nil => simp [Circuit.unitary]
  | cons g c ih =>
    rw [List.reverse_cons,circuit_unitary_append,circuit_unitary_cons]
    simp only [circuit_unitary_cons,circuit_unitary_nil,one_mul]
    rw [ih,star_mul,← embedOp_star,section5_gatesRev_star_self g.gate g.mem]

theorem section5_rev_realizable_adj {m : ℕ} {lc : LayeredCircuit m}
    (h : section5_RevRealizable lc) : section5_RevRealizable lc.adj := by
  obtain ⟨c,hc,hcu⟩ := h
  refine ⟨c.reverse,?_,?_⟩
  · simpa only [Circuit.size,List.length_reverse,LayeredCircuit.adj_size] using hc
  · rw [section5_rev_reverse_unitary,hcu,LayeredCircuit.adj_unitary]

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Comparing a score subregister and conditionally exchanging its complete record.
This is the reversible step in the maximum-column scan. -/

theorem section5_updateOn_single_update {k m : ℕ} (e : Fin k ↪ Fin m)
    (z : Qubits m) (i : Fin k) (v : Bool) :
    updateOn e z (Function.update (z ∘ e) i v)=Function.update z (e i) v := by
  classical
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨a,rfl⟩ := hj
    rw [updateOn_apply_emb]
    by_cases ha : a=i
    · subst a; simp
    · rw [Function.update_of_ne ha,Function.update_of_ne (e.injective.ne ha)]
      rfl
  · rw [updateOn_apply_not_mem e z _ hj,Function.update_of_ne]
    exact fun h => hj ⟨i,h.symm⟩





theorem section5_record_compare_A {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) (i : Fin w) :
    section5_record_compare_wires score A B ctrl hAB hcA hcB ⟨i.val,by omega⟩=A (score i) := by
  change section5_record_compare_wires score A B ctrl hAB hcA hcB
    (Fin.castAdd 1 (Fin.castAdd w i))=A (score i)
  exact (combineEmb_castAdd _ _ _ (Fin.castAdd w i)).trans (combineEmb_castAdd _ _ _ i)

theorem section5_record_compare_B {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) (i : Fin w) :
    section5_record_compare_wires score A B ctrl hAB hcA hcB ⟨w+i.val,by omega⟩=B (score i) := by
  change section5_record_compare_wires score A B ctrl hAB hcA hcB
    (Fin.castAdd 1 (Fin.natAdd w i))=B (score i)
  exact (combineEmb_castAdd _ _ _ (Fin.natAdd w i)).trans (combineEmb_natAdd _ _ _ i)

theorem section5_record_compare_ctrl {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) :
    section5_record_compare_wires score A B ctrl hAB hcA hcB ⟨w+w,by omega⟩=ctrl := by
  change section5_record_compare_wires score A B ctrl hAB hcA hcB
    (Fin.natAdd (w+w) (0:Fin 1))=ctrl
  exact combineEmb_natAdd _ _ _ _

theorem section5_record_compare_update {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (z : Qubits m) :
    let e := section5_record_compare_wires score A B ctrl hAB hcA hcB
    updateOn e z (Aux_w54_arith.ltRegFn w (z ∘ e))=
      Function.update z ctrl (xor (z ctrl)
        (decide (bitsToNatLSB (z ∘ A ∘ score) < bitsToNatLSB (z ∘ B ∘ score)))) := by
  classical
  let e := section5_record_compare_wires score A B ctrl hAB hcA hcB
  have hA : (fun i : Fin w => (z ∘ e) ⟨i.val,by omega⟩)=z ∘ A ∘ score := by
    funext i
    rw [Function.comp_apply,section5_record_compare_A]
    rfl
  have hB : (fun i : Fin w => (z ∘ e) ⟨w+i.val,by omega⟩)=z ∘ B ∘ score := by
    funext i
    rw [Function.comp_apply,section5_record_compare_B]
    rfl
  have hc : (z ∘ e) ⟨w+w,by omega⟩=z ctrl := by
    rw [Function.comp_apply,section5_record_compare_ctrl]
  change updateOn e z (Aux_w54_arith.ltRegFn w (z ∘ e))=_
  unfold Aux_w54_arith.ltRegFn
  rw [hA,hB,hc,section5_updateOn_single_update,section5_record_compare_ctrl]











theorem section5_combineEmb_range {m a b : ℕ} (A : Fin a ↪ Fin m) (B : Fin b ↪ Fin m)
    (hAB : ∀ i j, A i ≠ B j) {j : Fin m} (hj : j ∈ Set.range (combineEmb A B hAB)) :
    j ∈ Set.range A ∨ j ∈ Set.range B := by
  obtain ⟨i,rfl⟩ := hj
  induction i using Fin.addCases with
  | left i => exact Or.inl ⟨i,(combineEmb_castAdd A B hAB i).symm⟩
  | right i => exact Or.inr ⟨i,(combineEmb_natAdd A B hAB i).symm⟩

theorem section5_record_compare_off_range {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (j : Fin m) (hjA : j ∉ Set.range A) (hjB : j ∉ Set.range B) (hjc : j ≠ ctrl) :
    j ∉ Set.range (section5_record_compare_wires score A B ctrl hAB hcA hcB) := by
  intro hj
  have hor := section5_combineEmb_range
    (combineEmb (score.trans A) (score.trans B) (fun i j => hAB (score i) (score j)))
    (section5_boolean_wire1 ctrl) _ hj
  rcases hor with hscore | hctrl
  · have hs := section5_combineEmb_range (score.trans A) (score.trans B) _ hscore
    rcases hs with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact hjA ⟨score i,hi⟩
    · exact hjB ⟨score i,hi⟩
  · obtain ⟨i,hi⟩ := hctrl
    exact hjc hi.symm

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









@[simp] private lemma cuccaroWireEmb_val (w : ℕ) (u : Fin (1 + 2 * w)) :
    (cuccaroWireEmb w u).1 =
      if u.1 = 0 then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w, _⟩ : Fin ((w + w) + 1))
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl





















@[simp] private lemma cuccaroCarryShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w + 1)) :
    (cuccaroCarryShiftEmb w i).1 =
      if i.1 = 0 then 1 else if i.1 = 1 + 2 * w then 1 + 2 * (w + 1) else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1) + 1))
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), _⟩ else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl



lemma cuccaroCarryOut_size (w : ℕ) : (cuccaroCarryOut w).size = 14 * w + 1 := by
  induction w with
  | zero => simp [cuccaroCarryOut]
  | succ w ih =>
    simp only [cuccaroCarryOut, LayeredCircuit.seq_size, LayeredCircuit.adj_size,
      LayeredCircuit.mapWires_size, cuccaroMAJ_size, ih]
    omega





private lemma flipRegCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (flipRegCircuit w k hk).size = k := by
  induction k with
  | zero => simp [flipRegCircuit]
  | succ k ih => simp [flipRegCircuit, ih (by omega)]





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



lemma ltRegCircuit_size (w : ℕ) : (ltRegCircuit w).size = 16 * w + 1 := by
  dsimp only [ltRegCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, flipRegCircuit_size,
    cuccaroCarryOut_size]
  omega





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

/-! Actual NOT/CNOT/Toffoli implementations of the accepted linear-size adders. -/

theorem section5_rev_cuccaro_maj {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) :
    section5_RevRealizable (Aux_w54_arith.cuccaroMAJ c b a hcb hca hba) := by
  exact section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
    (section5_rev_realizable_seq (section5_rev_realizable_cnot _ _ _)
      (section5_rev_realizable_toffoli _ _ _ _ _ _))























end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Actual reversible register comparisons for squared-norm and maximum-column
selection. The accepted arithmetic foundation provides their exact basis action. -/

theorem section5_rev_carry_out (w : ℕ) :
    section5_RevRealizable (Aux_w54_arith.cuccaroCarryOut w) := by
  induction w with
  | zero => exact section5_rev_realizable_cnot _ _ _
  | succ w ih =>
    dsimp only [Aux_w54_arith.cuccaroCarryOut]
    have hm := section5_rev_cuccaro_maj
      (⟨0,by omega⟩ : Fin (1+2*(w+1)+1)) ⟨2,by omega⟩ ⟨1,by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    exact section5_rev_realizable_seq hm (section5_rev_realizable_seq
      (section5_rev_realizable_map_wires _ ih) (section5_rev_realizable_adj hm))

theorem section5_rev_flip_register (w k : ℕ) (hk : k ≤ w) :
    section5_RevRealizable (Aux_w54_arith.flipRegCircuit w k hk) := by
  induction k with
  | zero => exact section5_rev_realizable_id _
  | succ k ih =>
    exact section5_rev_realizable_seq (ih (by omega)) (section5_rev_realizable_not _)

theorem section5_rev_register_comparator (w : ℕ) :
    section5_RevRealizable (Aux_w54_arith.ltRegCircuit w) := by
  dsimp only [Aux_w54_arith.ltRegCircuit]
  have hf := section5_rev_realizable_map_wires (Aux_w54_arith.ltFlipEmb w)
    (section5_rev_flip_register w w le_rfl)
  exact section5_rev_realizable_seq hf (section5_rev_realizable_seq
    (section5_rev_realizable_map_wires _ (section5_rev_carry_out w)) hf)



theorem section5_embedded_register_comparator {m : ℕ} (w : ℕ)
    (emain : Fin (w+w+1) ↪ Fin m) (eanc : Fin 1 ↪ Fin m)
    (hdisj : ∀ i j, emain i ≠ eanc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w+1 ∧
      ∀ z : Qubits m, (∀ j, z (eanc j)=false) →
        act c.unitary (ket z)=ket (updateOn emain z (Aux_w54_arith.ltRegFn w (z ∘ emain))) := by
  obtain ⟨c,hc,hact⟩ := section5_embed_reversible_clean_permutation
    (Aux_w54_arith.ltRegCircuit w) (Aux_w54_arith.ltRegFn w)
    (section5_rev_register_comparator w) (Aux_w54_arith.ltRegCircuit_implements w)
    emain eanc hdisj
  exact ⟨c,hc.trans (Aux_w54_arith.ltRegCircuit_size w).le,hact⟩

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m) (anc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (hAa : ∀ i j, A i ≠ anc j) (hBa : ∀ i j, B i ≠ anc j) (hca : ∀ j, ctrl ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w+1+7*R ∧
      ∀ z : Qubits m, z ctrl=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (z' ∘ A=if bitsToNatLSB (z ∘ A ∘ score) < bitsToNatLSB (z ∘ B ∘ score)
            then z ∘ B else z ∘ A) ∧
          (∀ j, j ∉ Set.range A → j ∉ Set.range B → j ≠ ctrl → z' j=z j) ∧
          ∀ j, z' (anc j)=false := by
  classical
  let cmp := section5_record_compare_wires score A B ctrl hAB hcA hcB
  let sw := section5_record_swap_wires A B ctrl hAB hcA hcB
  have hcmpanc : ∀ i j, cmp i ≠ anc j := by
    intro i j hi
    exact section5_record_compare_off_range score A B ctrl hAB hcA hcB (anc j)
      (by rintro ⟨i,hi⟩; exact hAa i j hi)
      (by rintro ⟨i,hi⟩; exact hBa i j hi) (hca j).symm ⟨i,hi⟩
  obtain ⟨cc,hcc,hccact⟩ := section5_embedded_register_comparator w cmp anc hcmpanc
  obtain ⟨cs,hcs,hcsact⟩ := section5_embedded_controlled_swap_register R sw
  refine ⟨cc++cs,?_,?_⟩
  · simp only [Circuit.size,List.length_append] at *
    omega
  · intro z hzc hza
    let verdict := decide (bitsToNatLSB (z ∘ A ∘ score) < bitsToNatLSB (z ∘ B ∘ score))
    let z1 := Function.update z ctrl verdict
    let z2 := updateOn sw z1 (cswapRegFn R (z1 ∘ sw))
    have hcmpact : act cc.unitary (ket z)=ket z1 := by
      rw [hccact z hza,section5_record_compare_update,hzc,Bool.false_xor]
    have hz1A : z1 ∘ A=z ∘ A := by
      funext i
      exact Function.update_of_ne (hcA i).symm _ _
    have hz1B : z1 ∘ B=z ∘ B := by
      funext i
      exact Function.update_of_ne (hcB i).symm _ _
    have hctrl : z1 ctrl=verdict := Function.update_self _ _ _
    have hoff : ∀ j, j ∉ Set.range A → j ∉ Set.range B → j ≠ ctrl → z2 j=z j := by
      intro j hjA hjB hjc
      exact (updateOn_apply_not_mem sw z1 _
        (section5_record_swap_off_range A B ctrl hAB hcA hcB j hjA hjB hjc)).trans
          (Function.update_of_ne hjc _ _)
    refine ⟨z2,?_,?_,hoff,?_⟩
    · rw [section5_boolean_circuit_append,hcmpact,hcsact]
    · have hh := section5_record_swap_value_A A B ctrl hAB hcA hcB z1
      change z2 ∘ A=_ at hh
      rw [hctrl,hz1A,hz1B] at hh
      simpa only [verdict,decide_eq_true_eq] using hh
    · intro j
      exact (hoff (anc j) (by rintro ⟨i,hi⟩; exact hAa i j hi)
        (by rintro ⟨i,hi⟩; exact hBa i j hi) (hca j).symm).trans (hza j)
