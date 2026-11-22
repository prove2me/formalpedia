-- Prove2me | solution 1 for exists_g_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:42.534805+00:00
-- url     : https://prove2.me/submissions/7fab42af-f381-413c-bc17-6a35e1764c44

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_isUnit_intCast_of_natAbs_coprime
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (a b : ℤ) (hd : Nat.gcd b.natAbs m = 1)
    (hm : 0 < m) (hcard : (zmod_set m a b).card = 4) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ m - 2 ∧ zmod_set m a b =
        ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)).image ((b : ZMod m) * ·) := by
  have hm4 : 4 ≤ m := by
    haveI : NeZero m := ⟨by grind⟩
    linarith [Finset.card_le_univ (zmod_set m a b), ZMod.card m]
  haveI : NeZero m := ⟨by grind⟩
  have hub : IsUnit ((b : ℤ) : ZMod m) := isUnit_intCast_of_natAbs_coprime hd
  set bz : ZMod m := (b : ZMod m)
  set az : ZMod m := (a : ZMod m)
  set g' : ZMod m := bz⁻¹ * (bz - az)
  have hbg' : bz * g' = bz - az := by
    simp only [g', ← mul_assoc, ZMod.mul_inv_of_unit _ hub, one_mul]
  have hbg'1 : bz * (g' + 1) = 2 * bz - az := by rw [mul_add, mul_one, hbg']; ring
  have hset : zmod_set m a b = ({0, 1, g', g' + 1} : Finset (ZMod m)).image (bz * ·) := by
    simp only [zmod_set, Finset.image_insert, Finset.image_singleton]
    grind
  have hval : (g'.val : ZMod m) = g' := ZMod.natCast_zmod_val g'
  have hinj : Function.Injective (bz * · : ZMod m → ZMod m) := fun x y h => by
    simpa [← mul_assoc, ZMod.inv_mul_of_unit _ hub] using congr_arg (bz⁻¹ * ·) h
  have hcard4 : ({0, 1, g', g' + 1} : Finset (ZMod m)).card = 4 := by
    rwa [hset, Finset.card_image_of_injective _ hinj] at hcard
  refine ⟨g'.val, ?_, ?_, ?_⟩
  · by_contra! hlt
    have hcases : g'.val = 0 ∨ g'.val = 1 := by grind
    rcases hcases with h | h
    · have hg'0 : g' = 0 := by rw [← hval, h, Nat.cast_zero]
      grind
    · have hg'1 : g' = 1 := by rw [← hval, h, Nat.cast_one]
      grind
  · by_contra! hgt
    have hval_lt := ZMod.val_lt g'
    have hgm1 : g'.val = m - 1 := by grind
    have hg'p1 : g' + 1 = 0 := by rw [← hval, hgm1, Nat.cast_sub (by grind),
        Nat.cast_one, ZMod.natCast_self, zero_sub, neg_add_cancel]
    grind [Finset.card_le_three]
  · grind
