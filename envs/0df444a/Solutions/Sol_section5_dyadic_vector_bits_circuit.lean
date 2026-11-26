-- Prove2me | solution 1 for section5_dyadic_vector_bits_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:14.645595+00:00
-- url     : https://prove2.me/submissions/6ba78ca5-dec3-4858-a97c-a5af76fd9c23

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
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_dyadic_offset_bits_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m r N d b : ℕ}
    (data : Fin r ↪ Fin m) (src : Fin N → Fin (d+1) ↪ Fin r)
    (dst : Fin N → Fin (b+1) ↪ Fin m) (s : ℕ) (hfit : s+(b+1) ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e f, dst i e ≠ dst j f)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1)*N ∧
      ∀ z : Qubits m, (∀ i e, z (dst i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (dst i)) → z' j=z j) ∧
          ∀ i, z' ∘ dst i=section5_dyadic_offset_bits s b hfit (z ∘ data ∘ src i) := by
  classical
  let aux : Fin 0 → Fin m := Fin.elim0
  have hblocks : ∀ i : Fin N, ∃ c : Circuit gatesRev m,
      c.size ≤ 2*(b+1) ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ e, z (dst i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range (dst i) → z' j=z j) ∧
          z' ∘ dst i=section5_dyadic_offset_bits s b hfit (z ∘ data ∘ src i) := by
    intro i
    obtain ⟨c,hc,hact⟩ := section5_dyadic_offset_bits_circuit ((src i).trans data) (dst i)
      s hfit (fun e f => hdata i _ f)
    refine ⟨c,hc,?_⟩
    intro z hza hz0
    refine ⟨Thm410Router.updateOn (dst i) z
      (section5_dyadic_offset_bits s b hfit (z ∘ data ∘ src i)),hact z hz0,?_,?_⟩
    · intro j hj
      exact Thm410Router.updateOn_apply_not_mem (dst i) z _ hj
    · funext e
      exact Thm410Router.updateOn_apply_emb (dst i) z _ e
  choose cs hs ha using hblocks
  obtain ⟨c,hc,hact⟩ := section5_clean_batch_all cs dst data aux hs hpair hdata
    (fun i j => Fin.elim0 j) (fun z => z)
    (fun i z => section5_dyadic_offset_bits s b hfit (z ∘ src i)) ha
  exact ⟨c,hc,fun z hz0 => hact z (fun j => Fin.elim0 j) hz0⟩
