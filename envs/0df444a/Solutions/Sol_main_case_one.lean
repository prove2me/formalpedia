-- Prove2me | solution 1 for main_case_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:21.894173+00:00
-- url     : https://prove2.me/submissions/306c7cd1-c1d4-4f08-ad40-3c416645241a

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_hasPolychromColouring_mul_unit
import Theorems.Thm_case_one_dispatch
import Theorems.Thm_case_one_complement
import Theorems.Thm_exists_g_of_coprime
import Theorems.Thm_isUnit_intCast_of_natAbs_coprime
import Theorems.Thm_zmod_set_swap


set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (a b : ℤ) (hm : m ≥ 289) (hcard : (zmod_set m a b).card = 4)
    (h_gcd : Nat.gcd b.natAbs m = 1 ∨ Nat.gcd (b - a).natAbs m = 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  suffices ∀ a' b' : ℤ, Nat.gcd b'.natAbs m = 1 → (zmod_set m a' b').card = 4 →
      HasPolychromColouring (Fin 3) (zmod_set m a' b') by
    rcases h_gcd with hb | hba
    · exact this a b hb hcard
    · rw [← zmod_set_swap m a b]
      apply this (-a) (b - a) hba
      rwa [zmod_set_swap]
  intro a' b' hd hcard'
  obtain ⟨g, hg_ge, hg_le, hset⟩ := exists_g_of_coprime m a' b' hd (by grind) hcard'
  obtain ⟨u, hu⟩ := isUnit_intCast_of_natAbs_coprime hd
  rw [hset, ← hu, hasPolychromColouring_mul_unit]
  by_cases hg_half : g ≤ m / 2
  · exact case_one_dispatch m g hm hg_ge hg_half
  · push Not at hg_half
    rw [← case_one_complement m g (by grind)]
    exact case_one_dispatch m (m - g) hm (by grind) (by grind)
