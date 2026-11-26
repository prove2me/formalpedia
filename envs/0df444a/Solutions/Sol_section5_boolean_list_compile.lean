-- Prove2me | solution 1 for section5_boolean_list_compile
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:32.993697+00:00
-- url     : https://prove2.me/submissions/803654f4-0189-4823-91d5-9ef856513037

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5BooleanCircuitCompilation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Every well-formed Boolean straight-line program has a linear-size reversible implementation. -/



theorem section5_boolean_memory_append (m p : ℕ) (hp : p < m)
    (v : List Bool) (hv : v.length=p) (b : Bool) :
    Function.update (section5_boolean_memory m v) ⟨p,hp⟩ b = section5_boolean_memory m (v++[b]) := by
  classical
  funext i
  by_cases hip : i.val=p
  · have hieq : i=(⟨p,hp⟩ : Fin m) := Fin.ext hip
    subst i
    simp only [Function.update_self,section5_boolean_memory]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [← hv]
  · have hne : i ≠ (⟨p,hp⟩ : Fin m) := by intro h; exact hip (congrArg Fin.val h)
    rw [Function.update_of_ne hne]
    dsimp only [section5_boolean_memory]
    by_cases hil : i.val < v.length
    · exact (List.getD_append _ _ _ _ hil).symm
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]







end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/













































theorem section5_boolean_circuit_nil {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary ([] : Circuit gatesRev m)) ψ=ψ := by
  ext z
  simp [Circuit.unitary,act]





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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution (l : List BoolGate) (m p : ℕ)
    (hspace : p+l.length ≤ m)
    (hwf : ∀ k (hk : k < l.length),
      (l[k]).a < p+k ∧ ((l[k]).op=BoolOp.not ∨ (l[k]).b < p+k)) :
    ∃ c : Circuit gatesRev m, c.size ≤ 3*l.length ∧
      ∀ v : List Bool, v.length=p →
        act c.unitary (ket (section5_boolean_memory m v))=
          ket (section5_boolean_memory m (section5_boolean_values l v)) := by
  classical
  induction l generalizing p with
  | nil =>
    refine ⟨[],by norm_num [Circuit.size],?_⟩
    intro v hv
    exact section5_boolean_circuit_nil (ket (section5_boolean_memory m v))
  | cons g l ih =>
    have hspace' : p+(l.length+1) ≤ m := by simpa only [List.length_cons] using hspace
    have hp : p < m := by omega
    have hhead := hwf 0 (by simp)
    simp only [List.getElem_cons_zero,add_zero] at hhead
    have htail : ∀ k (hk : k < l.length),
        (l[k]).a < (p+1)+k ∧ ((l[k]).op=BoolOp.not ∨ (l[k]).b < (p+1)+k) := by
      intro k hk
      have h := hwf (k+1) (by simp; omega)
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    obtain ⟨d,hdsize,hdact⟩ := ih (p+1) (by omega) htail
    let bv := if g.op=BoolOp.not then g.a else g.b
    have hb : bv < p := by
      dsimp only [bv]
      split_ifs with h
      · exact hhead.1
      · exact hhead.2.resolve_left h
    let a : Fin m := ⟨g.a,lt_trans hhead.1 hp⟩
    let b : Fin m := ⟨bv,lt_trans hb hp⟩
    let t : Fin m := ⟨p,hp⟩
    have hat : a ≠ t := by intro h; have := congrArg Fin.val h; dsimp only [a,t] at this; omega
    have hbt : b ≠ t := by intro h; have := congrArg Fin.val h; dsimp only [b,t] at this; omega
    let c := section5_boolean_gate_circuit g.op a b t hat hbt
    have hcsize : c.size ≤ 3 := section5_boolean_gate_size g.op a b t hat hbt
    refine ⟨c++d,?_,?_⟩
    · change (c++d).length ≤ 3*(g::l).length
      rw [List.length_append,List.length_cons]
      change c.length ≤ 3 at hcsize
      change d.length ≤ 3*l.length at hdsize
      omega
    · intro v hv
      have htarget : section5_boolean_memory m v t=false :=
        List.getD_eq_default _ _ (by simpa only [hv] using le_refl p)
      have hval : section5_bool_value g.op (section5_boolean_memory m v a)
          (section5_boolean_memory m v b)=g.value v := by
        change section5_bool_value g.op (v.getD g.a false) (v.getD bv false)=g.value v
        cases hop : g.op <;> simp [section5_bool_value,BoolGate.value,hop,bv]
      rw [section5_boolean_circuit_append,section5_boolean_gate_action,htarget,hval,Bool.false_xor]
      rw [section5_boolean_memory_append m p hp v hv,hdact _ (by simp [hv])]
      rfl
