-- Prove2me | solution 1 for section5_single_qex_vote_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:33:31.846586+00:00
-- url     : https://prove2.me/submissions/4591153c-2a7b-487b-9dda-8ec46184b946

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
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
import Theorems.Thm_section5_uniform_window_comparator
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/











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



























theorem section5_embedded_cnot_target {m : ℕ} (a t : Fin m) (hat : a ≠ t) (x : Qubits m) :
    act (embedOp (Gate.ofMatrix2 cnot).mat (section5_boolean_wire2 a t hat)) (ket x)=
      ket (Function.update x t (xor (x t) (x a))) := by
  have hact := section5_embed_classical_gate_action (section5_boolean_wire2 a t hat)
    _ _ section5_cnot_matrix_action x
  rw [section5_replace_wires_eq_update _ _ _ 1 (by
    intro i hi
    fin_cases i
    · rfl
    · exact (hi rfl).elim)] at hact
  exact hact



theorem section5_boolean_circuit_cons {m : ℕ} (g : GateApp gatesRev m) (c : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (g::c)) ψ=act c.unitary (act (embedOp g.gate.mat g.wires) ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z

theorem section5_boolean_circuit_nil {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary ([] : Circuit gatesRev m)) ψ=ψ := by
  ext z
  simp [Circuit.unitary,act]

















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

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm410Router

/-! A QEX orientation vote with the exact public label convention. Its circuit
is independent of the target, and its gate count is independent of grid precision. -/

theorem section5_ltf_binary {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ltf w θ x=1 ∨ ltf w θ x= -1 := by
  unfold ltf sgn
  split_ifs <;> simp



end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Three label disagreements and their majority require six reversible gates.
The predictor sign bits are reused as the three disagreement bits. -/

theorem section5_label_bits_mismatch (a b : ℤ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    xor (decide (a= -1)) (decide (b= -1))=decide (a ≠ b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem section5_comparator_negative_bit (a : ℤ) (ha : a=1 ∨ a= -1) (b : Bool)
    (hb : a=1 ↔ b=false) : b=decide (a= -1) := by
  rcases ha with rfl | rfl <;> cases b <;> simp_all





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm410Router
theorem solution {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t label : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) (hlp : label ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ 128*(n+a+34)^4+1 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ e, z (p e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=
            xor (decide (ltf (WithLp.toLp 2 fun i => readFp (ov i) f z) 0
              (section5_bounded_window_vector q (gridPoint (z ∘ ex)))= -1)) (z label) ∧
          ∀ w : EuclideanSpace ℝ (Fin n),
            z label=decide (ltf w 0 (gridPoint (z ∘ ex))= -1) →
              z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=
                section5_quantized_vote w (WithLp.toLp 2 fun i => readFp (ov i) f z) (z ∘ ex) := by
  classical
  obtain ⟨cc,hc,hact⟩ := section5_uniform_window_comparator hn hgrid f ov ex p anc hpa t
    htp hta hut hxt hup hxp hxa
  let target := p (Fin.last (n+a+(2*section5_window_precision n+1)))
  have hlt : label ≠ target := fun h => hlp ⟨_,h.symm⟩
  let cx : Circuit gatesRev m := [section5_rev_cnot (section5_boolean_wire2 label target hlt)]
  refine ⟨cc++cx,?_,?_⟩
  · simpa only [Circuit.size,List.length_append,cx,List.length_cons,List.length_nil] using
      Nat.add_le_add_right hc 1
  · intro z hzt hza hzp
    obtain ⟨z1,hz1,hoff,hsign⟩ := hact z hzt hza hzp
    let z2 := Function.update z1 target (xor (z1 target) (z1 label))
    have hlabel : z1 label=z label := hoff label hlp
    have hpred := section5_comparator_negative_bit _
      (section5_ltf_binary (WithLp.toLp 2 fun i => readFp (ov i) f z) 0
        (section5_bounded_window_vector q (gridPoint (z ∘ ex)))) (z1 target) hsign
    have hbit : z2 target=xor (decide (ltf (WithLp.toLp 2 fun i => readFp (ov i) f z) 0
        (section5_bounded_window_vector q (gridPoint (z ∘ ex)))= -1)) (z label) := by
      change Function.update z1 target (xor (z1 target) (z1 label)) target=_
      rw [Function.update_self,hpred,hlabel]
    refine ⟨z2,?_,?_,hbit,?_⟩
    · rw [section5_boolean_circuit_append,hz1]
      simp only [cx,section5_boolean_circuit_cons,section5_rev_cnot,
        section5_embedded_cnot_target,section5_boolean_circuit_nil]
      rfl
    · intro j hj
      have hjt : j ≠ target := fun h => hj ⟨_,h.symm⟩
      exact (Function.update_of_ne hjt _ _).trans (hoff j hj)
    · intro w htruth
      rw [hbit,htruth,Bool.xor_comm]
      exact section5_label_bits_mismatch _ _ (section5_ltf_binary w 0 _)
        (section5_ltf_binary (WithLp.toLp 2 fun i => readFp (ov i) f z) 0 _)
