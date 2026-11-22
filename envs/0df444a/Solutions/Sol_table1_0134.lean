-- Prove2me | solution 1 for table1_0134
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:47:05.997253+00:00
-- url     : https://prove2.me/submissions/75858aec-8ce9-4627-92bc-e0680ede5bd5

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Theorems.Thm_blockColor_polychrom
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section BlockColorInfra
private lemma frobenius_consec {rA m : ℕ} (hrA : 1 < rA) (hm : m ≥ rA * (rA - 1)) :
    ∃ h k, rA * h + (rA + 1) * k = m ∧ 0 < h + k := by
  obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le rA (rA + 1) m
    (by rw [(Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).gcd_eq_one]; exact one_dvd _)
    (by grind [Nat.pred_eq_sub_one, mul_comm rA (rA - 1)])
  refine ⟨a, b, by grind [mul_comm a rA, mul_comm b (rA + 1)], ?_⟩
  have : 0 < rA * (rA - 1) := Nat.mul_pos (by omega) (by omega)
  grind
private lemma hasPolychromColouring_of_cyclic {m : ℕ} [NeZero m] [Fact (1 < m)]
    (c : ℕ → Fin 3) (S : Finset (ZMod m))
    (hpoly : ∀ n : ZMod m, ∀ k : Fin 3, ∃ a ∈ S, c (n + a).val = k) :
    HasPolychromColouring (Fin 3) S :=
  ⟨fun x => c x.val, hpoly⟩
end BlockColorInfra
section Table1
variable (m : ℕ)
private lemma table1_of_blockColor (A B : List (Fin 3)) (offsets : List ℕ) (S : Finset (ZMod m))
    (hA : 2 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hpairs : checkBlockPairs offsets A B = true)
    (hm : m ≥ A.length * (A.length - 1))
    (hS : ∀ a : ZMod m, a ∈ S ↔ ∃ s ∈ offsets, (s : ZMod m) = a) :
    HasPolychromColouring (Fin 3) S := by
  have hA_lt_m : A.length < m := by
    have : A.length * 2 ≤ A.length * (A.length - 1) := by gcongr; omega
    omega
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  obtain ⟨h, k, hm_eq, hhk⟩ := frobenius_consec (by omega : 1 < A.length) hm
  apply hasPolychromColouring_of_cyclic (blockColorVal A B h) S
  intro n target
  obtain ⟨s, hs_mem, hs_eq⟩ := blockColor_polychrom A B offsets (by omega) hBlen hmaxOff
    hpairs hhk (by grind) (ZMod.val_lt n) target
  refine ⟨(s : ZMod m), (hS _).mpr ⟨s, hs_mem, rfl⟩, ?_⟩
  have : s < m := lt_of_le_of_lt (le_trans (List.le_max_of_le' 0 hs_mem le_rfl) hmaxOff) hA_lt_m
  rwa [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt this]
end Table1
end

set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (hm : m ≥ 30) : HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,1,2,1,2] [0,0,0,1,2,1,2] [0,1,3,4] {0, 1, 3, 4}
    (by simp) (by simp) (by decide) (by decide) hm (by intro a; simp; tauto)
