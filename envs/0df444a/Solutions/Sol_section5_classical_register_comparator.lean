-- Prove2me | solution 1 for section5_classical_register_comparator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:06.334256+00:00
-- url     : https://prove2.me/submissions/ad6367aa-d137-479f-be68-f15f4f175e23

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
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_ltRegCircuit_implements
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

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router




























/-! ### Part 2: Zero-Ancilla Register Primitives -/












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/





@[simp] private lemma cuccaroMAJ_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroMAJ c b a hcb hca hba).size = 7 := by
  simp [cuccaroMAJ]

















































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





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution (w : ℕ) :
    ∃ c : Circuit gatesRev ((w+w+1)+1), c.size ≤ 16*w+1 ∧
      ∀ x : Qubits (w+w+1),
        act c.unitary (ket (padZero (w+w+1) 1 x))=
          ket (padZero (w+w+1) 1 (Aux_w54_arith.ltRegFn w x)) := by
  obtain ⟨c,hc,hcu⟩ := section5_rev_register_comparator w
  refine ⟨c,hc.trans (Aux_w54_arith.ltRegCircuit_size w).le,?_⟩
  intro x
  rw [hcu]
  exact act_ket_of_implementsOnClean_perm (Aux_w54_arith.ltRegCircuit_implements w) x
