-- Prove2me | solution 1 for section5_weighted_accumulator_value
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:05.727101+00:00
-- url     : https://prove2.me/submissions/62019533-212a-46ff-ab41-887390cb389a

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
import Definitions.Def_Section5Verified_Section5WeightedAccumulator
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A clean reversible accumulator for an arbitrary binary weighted sum. The gate count
is linear in the accumulator width and the number of summands. -/





theorem section5_weighted_step_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (a : Fin m × ℕ) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_weighted_step p a z j=z j := by
  unfold section5_weighted_step
  split_ifs
  · exact updateOn_apply_not_mem p z _ hj
  · rfl





theorem section5_bitsToNatLSB_mod (w val : ℕ) :
    bitsToNatLSB (natToBitsLSB w val)=val%2^w := by
  have heq : natToBitsLSB w val=natToBitsLSB w (val%2^w) := by
    funext i
    simp [natToBitsLSB,Nat.testBit_mod_two_pow,i.isLt]
  rw [heq]
  exact bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m w : ℕ}
    (p : Fin w ↪ Fin m) (ops : List (Fin m × ℕ))
    (hctrl : ∀ a ∈ ops, ∀ i, a.1 ≠ p i) (z : Qubits m) :
    bitsToNatLSB (section5_weighted_eval p ops z ∘ p)=
      (bitsToNatLSB (z ∘ p)+section5_binary_weighted_sum ops z)%2^w := by
  induction ops generalizing z with
  | nil => simp [section5_weighted_eval,section5_binary_weighted_sum,
      Nat.mod_eq_of_lt (bitsToNatLSB_lt w (z ∘ p))]
  | cons a ops ih =>
    let z' := section5_weighted_step p a z
    change bitsToNatLSB (section5_weighted_eval p ops z' ∘ p)=_
    rw [ih (fun b hb => hctrl b (by simp [hb]))]
    have hsum : section5_binary_weighted_sum ops z'=section5_binary_weighted_sum ops z := by
      unfold section5_binary_weighted_sum
      congr 1
      apply List.map_congr_left
      intro b hb
      have hb' : b.1 ∉ Set.range p := by
        rintro ⟨i,hi⟩
        exact hctrl b (by simp [hb]) i hi.symm
      rw [show z' b.1=z b.1 from section5_weighted_step_off p a z b.1 hb']
    rw [hsum]
    have hv : bitsToNatLSB (z' ∘ p)=
        if z a.1 then (a.2%2^w+bitsToNatLSB (z ∘ p))%2^w else bitsToNatLSB (z ∘ p) := by
      dsimp only [z',section5_weighted_step]
      split_ifs
      · have heq : updateOn p z (natToBitsLSB w (a.2%2^w+bitsToNatLSB (z ∘ p))) ∘ p =
            natToBitsLSB w (a.2%2^w+bitsToNatLSB (z ∘ p)) := by
          funext i
          exact updateOn_apply_emb p z _ i
        rw [heq,section5_bitsToNatLSB_mod]
      · rfl
    rw [hv]
    simp only [section5_binary_weighted_sum,List.map_cons,List.sum_cons]
    split_ifs <;> simp only [Nat.mod_add_mod,Nat.add_mod_mod,zero_add]
    congr 1
    omega
