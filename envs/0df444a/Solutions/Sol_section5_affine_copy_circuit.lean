-- Prove2me | solution 1 for section5_affine_copy_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:35.406045+00:00
-- url     : https://prove2.me/submissions/415c5208-d60d-4ced-b1e9-5a7c49f683db

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
import Theorems.Thm_section5_affine_copy_prefix_action
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm410Router

/-! An affine copy of arbitrarily selected input bits into a disjoint register.
Each output takes at most two reversible gates, even if input bits are repeated. -/







theorem section5_affine_copy_prefix_size {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j)
    (k : ℕ) (hk : k ≤ w) :
    (section5_affine_copy_prefix src dst neg hdisj k hk).size ≤ 2*k := by
  induction k with
  | zero => simp [section5_affine_copy_prefix,Circuit.size]
  | succ k ih =>
    have h := ih (by omega)
    dsimp only [section5_affine_copy_prefix]
    simp only [Circuit.size,List.length_append]
    change (section5_affine_copy_prefix src dst neg hdisj k _).length ≤ _ at h
    cases hn : neg ⟨k,by omega⟩ <;>
      simp [hn,section5_boolean_gate_circuit,Circuit.size] <;> omega





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm410Router
theorem solution {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*w ∧
      ∀ z : Qubits m, (∀ i, z (dst i)=false) →
        act c.unitary (ket z)=ket (updateOn dst z (section5_affine_bit src neg z)) := by
  refine ⟨section5_affine_copy_prefix src dst neg hdisj w le_rfl,
    section5_affine_copy_prefix_size src dst neg hdisj w le_rfl,?_⟩
  intro z hz
  rw [section5_affine_copy_prefix_action]
  congr 1
  unfold section5_affine_prefix_state
  congr 1
  funext i
  simp [i.isLt,hz i]
