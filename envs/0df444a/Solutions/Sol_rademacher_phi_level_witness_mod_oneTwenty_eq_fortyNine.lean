-- Prove2me | solution 1 for rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2a3eafcb-a5f9-5ff5-9059-9001a26973ba

import Definitions.Def_NumberTheory_DedekindSum
import Theorems.Thm_dedekindSum_add_dedekindSum
import Theorems.Thm_dedekindSum_one_left
import Theorems.Thm_dedekindSum_natCast_sub_one
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine

theorem solution (j : ℕ) : 12 * ((((24 * j + 10 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((120 * j + 49 : ℕ) : ℚ)) / (12 * ((120 * j + 49 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (120 * j + 49)) = ((Nat.gcd ((120 * j + 49) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 2)) ∧ Nat.Coprime (2 * j + 1) (10 * j + 4) := by
  refine ⟨?_, ?_⟩
  · have hcop : Nat.Coprime 5 (120 * j + 49) :=
      Nat.isCoprime_iff_coprime.mp ⟨24 * j + 10, -1, by push_cast; ring⟩
    have hrec := dedekindSum_add_dedekindSum 5 (120 * j + 49) (by norm_num) (by positivity) hcop
    have hper : dedekindSum ((120 * j + 49 : ℕ) : ℤ) 5 = dedekindSum 4 5 := by
      rw [← dedekindSum_add_mul 4 (24 * j + 9) 5]
      congr 1
      push_cast
      ring
    have h45 : dedekindSum 4 5 = -(1 / 5) := by
      have h1 := dedekindSum_natCast_sub_one 5
      have h2 := dedekindSum_one_left 5
      rw [show ((5 : ℕ) : ℤ) - 1 = 4 by norm_num] at h1
      rw [h1, h2]
      norm_num
    have h51 : dedekindSum 5 1 = 0 := dedekindSum_one_right 5
    have hs : dedekindSum 5 (120 * j + 49) = ((5 : ℚ) / ((120 * j + 49 : ℕ) : ℚ) + ((120 * j + 49 : ℕ) : ℚ) / 5
        + 1 / ((5 : ℚ) * ((120 * j + 49 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 5 := by
      have h := hrec
      rw [hper, h45] at h
      push_cast at h ⊢
      linarith
    have hgcd : Nat.gcd ((120 * j + 49) - 1) 12 = 12 := by
      rw [show (120 * j + 49) - 1 = 12 * (10 * j + 4) by omega]
      exact Nat.gcd_eq_right (Dvd.intro _ rfl)
    rw [h51, hs, hgcd]
    have hne : ((120 * j + 49 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · exact Nat.isCoprime_iff_coprime.mp ⟨5, -1, by push_cast; ring⟩

end S_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine
end P2MW
export P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine (solution)
