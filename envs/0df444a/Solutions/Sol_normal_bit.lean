-- Prove2me | solution 1 for normal_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:11.432362+00:00
-- url     : https://prove2.me/submissions/e8f2dc2d-2b27-4285-b54e-339acb23d150

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
import Theorems.Thm_zmod_set_card_eq_four
import Theorems.Thm_gcd_coprime_of_gcd_abc
import Theorems.Thm_hasPolychromColouring_of_zmod_set
import Theorems.Thm_main_case_one
import Theorems.Thm_main_case_two


set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → 289 ≤ c → Finset.gcd {a, b, c} id = 1 →
          HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hc hgcd
  set m := (c - a + b).toNat
  have hm_eq : (m : ℤ) = c - a + b := Int.toNat_of_nonneg (by grind)
  have hm_pos : 0 < m := by grind
  have hcard := zmod_set_card_eq_four ha hab (by linarith)
  apply hasPolychromColouring_of_zmod_set hm_eq
  set d₁ := Nat.gcd b.natAbs m
  set d₂ := Nat.gcd (b - a).natAbs m
  by_cases hmin : min d₁ d₂ = 1
  · apply main_case_one m a b (by grind) hcard
    grind
  · have : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    exact main_case_two (by grind) (gcd_coprime_of_gcd_abc hm_eq hgcd) (by grind)
