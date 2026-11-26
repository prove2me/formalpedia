-- Prove2me | solution 1 for section5_affine_copy_prefix_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:31.816068+00:00
-- url     : https://prove2.me/submissions/efcf9ae0-022e-4e2c-b39c-e4e28a5cac66

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/













































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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm410Router
theorem solution {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j)
    (k : ℕ) (hk : k ≤ w) (z : Qubits m) :
    act (section5_affine_copy_prefix src dst neg hdisj k hk).unitary (ket z)=
      ket (section5_affine_prefix_state src dst neg k z) := by
  classical
  induction k with
  | zero =>
    rw [section5_affine_copy_prefix,section5_boolean_circuit_nil]
    congr 1
    funext j
    dsimp only [section5_affine_prefix_state]
    by_cases hj : j ∈ Set.range dst
    · obtain ⟨i,rfl⟩ := hj
      simp [updateOn_apply_emb]
    · exact (updateOn_apply_not_mem dst z _ hj).symm
  | succ k ih =>
    let i : Fin w := ⟨k,by omega⟩
    let z' := section5_affine_prefix_state src dst neg k z
    have hsrc (j : Fin w) : z' (src j)=z (src j) :=
      updateOn_apply_not_mem dst z _ (by rintro ⟨l,hl⟩; exact hdisj j l hl.symm)
    have htgt : z' (dst i)=z (dst i) := by
      change updateOn dst z _ (dst i)=_
      rw [updateOn_apply_emb,if_neg (by dsimp [i]; omega)]
    have hval : section5_bool_value (if neg i then .not else .and)
        (z' (src i)) (z' (src i))=section5_affine_bit src neg z i := by
      rw [hsrc]
      cases hn : neg i <;> simp [hn,section5_bool_value,section5_affine_bit]
    dsimp only [section5_affine_copy_prefix]
    rw [section5_boolean_circuit_append,ih,section5_boolean_gate_action]
    change ket (Function.update z' (dst i)
      (xor (z' (dst i)) (section5_bool_value (if neg i then .not else .and)
        (z' (src i)) (z' (src i)))))=_
    rw [hval,htgt]
    congr 1
    funext j
    by_cases hj : j ∈ Set.range dst
    · obtain ⟨l,rfl⟩ := hj
      change Function.update z' (dst i) _ (dst l)=updateOn dst z _ (dst l)
      rw [updateOn_apply_emb]
      by_cases hli : l=i
      · subst l
        rw [Function.update_self,if_pos (by dsimp [i]; omega)]
      · rw [Function.update_of_ne (dst.injective.ne hli)]
        change updateOn dst z _ (dst l)=_
        rw [updateOn_apply_emb]
        have hlk : l.val ≠ k := by intro h; exact hli (Fin.ext h)
        by_cases hl : l.val < k <;> simp [hl,show (l.val < k+1) ↔ (l.val < k) by omega]
    · rw [Function.update_of_ne (by intro h; exact hj ⟨i,h.symm⟩)]
      exact (updateOn_apply_not_mem dst z _ hj).trans (updateOn_apply_not_mem dst z _ hj).symm
