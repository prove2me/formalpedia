-- Prove2me | solution 1 for section5_classical_adder_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:24.259957+00:00
-- url     : https://prove2.me/submissions/17739e56-7de9-411c-8793-511600f75fae

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
import Theorems.Thm_Aux_w54_arith_addInPlaceCircuit_implements
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

















end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution (w : ℕ) :
    ∃ c : Circuit gatesRev ((w+w)+1), c.size ≤ 14*w ∧
      ∀ x : Qubits (w+w),
        act c.unitary (ket (padZero (w+w) 1 x))=
          ket (padZero (w+w) 1 (Aux_w54_arith.addInPlaceFn w x)) := by
  obtain ⟨c,hc,hcu⟩ := section5_rev_adder w
  refine ⟨c,hc.trans (Aux_w54_arith.addInPlaceCircuit_size w).le,?_⟩
  intro x
  rw [hcu]
  exact act_ket_of_implementsOnClean_perm (Aux_w54_arith.addInPlaceCircuit_implements w) x
