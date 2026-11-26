-- Prove2me | solution 1 for section5_dyadic_offset_bits_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:59.373571+00:00
-- url     : https://prove2.me/submissions/be0b4643-67b6-4287-8aba-caea0f966510

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Mathlib
import Theorems.Thm_section5_affine_copy_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m W b : ℕ}
    (src : Fin W ↪ Fin m) (dst : Fin (b+1) ↪ Fin m) (s : ℕ) (hfit : s+(b+1) ≤ W)
    (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1) ∧
      ∀ z : Qubits m, (∀ j, z (dst j)=false) →
        act c.unitary (ket z)=ket (Thm410Router.updateOn dst z
          (section5_dyadic_offset_bits s b hfit (z ∘ src))) := by
  let source : Fin (b+1) → Fin m := fun i => src ⟨s+i.val,by omega⟩
  let invert : Fin (b+1) → Bool := fun i => decide (i=Fin.last b)
  obtain ⟨c,hc,hact⟩ := section5_affine_copy_circuit source dst invert (fun i j => hdisj _ j)
  refine ⟨c,hc,?_⟩
  intro z hz
  rw [hact z hz]
  congr 2
  funext i
  by_cases hi : i=Fin.last b
  · subst i
    simp [section5_affine_bit,invert,source,section5_dyadic_offset_bits,section5_offset_top_bit,
      section5_shifted_bits]
  · simp [section5_affine_bit,invert,source,section5_dyadic_offset_bits,section5_offset_top_bit,
      section5_shifted_bits,hi]
