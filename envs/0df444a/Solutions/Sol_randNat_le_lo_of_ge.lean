-- Prove2me | solution 1 for randNat_le_lo_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:15:10.927278+00:00
-- url     : https://prove2.me/submissions/aa3826be-8323-48a5-9be3-036505c81d4a

import Definitions.Def_MillerRabin_StrongProbable
import Definitions.Def_MillerRabin_MillerRabin
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false

theorem _root_.solution {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≥ hi) :
    (randNat g lo hi).1 ≤ lo := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact randNat_le_hi g hi hi h
  simp [randNat, h]
  have (n : ℕ) : n % (lo - hi + 1) ≤ lo - hi := Nat.lt_succ.mp (Nat.mod_lt n (by omega))
  grw [this]
  omega
