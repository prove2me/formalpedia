-- Prove2me | solution 1 for rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0748387c-f4b0-5530-b4fc-f35ff2affa52

import Definitions.Def_NumberTheory_DedekindSum
import Theorems.Thm_dedekindSum_add_dedekindSum
import Theorems.Thm_dedekindSum_one_left
import Theorems.Thm_dedekindSum_natCast_sub_one
import Theorems.Thm_dedekindSum_of_mul_modEq_one
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne

theorem solution (j : ℕ) : 12 * ((((45 * j + 23 : ℕ) + 8 : ℤ) : ℚ) * (1 - ((120 * j + 61 : ℕ) : ℚ)) / (12 * ((120 * j + 61 : ℕ) : ℚ)) + dedekindSum 8 1 - dedekindSum 8 (120 * j + 61)) = ((Nat.gcd ((120 * j + 61) - 1) 12 : ℕ) : ℚ) * (-(5 * (j : ℤ) + 3)) ∧ Nat.Coprime (Int.natAbs (-(5 * (j : ℤ) + 3))) (((120 * j + 61) - 1) / Nat.gcd ((120 * j + 61) - 1) 12) := by
  have hgcd : Nat.gcd ((120 * j + 61) - 1) 12 = 12 := by
    rw [show (120 * j + 61) - 1 = 12 * (10 * j + 5) by omega]
    exact Nat.gcd_eq_right (Dvd.intro _ rfl)
  refine ⟨?_, ?_⟩
  ·
    have h12 : dedekindSum 1 2 = 0 := by rw [dedekindSum_one_left 2]; norm_num
    have h52 : dedekindSum ((5 : ℕ) : ℤ) 2 = 0 := by
      rw [show ((5 : ℕ) : ℤ) = 1 + 2 * (2 : ℕ) by norm_num, dedekindSum_add_mul]; exact h12
    have hrec25 := dedekindSum_add_dedekindSum 2 5 (by norm_num) (by norm_num) (by norm_num)
    have h25 : dedekindSum 2 5 = 0 := by rw [h52] at hrec25; push_cast at hrec25 ⊢; linarith
    have h35 : dedekindSum 3 5 = 0 := by
      have := dedekindSum_of_mul_modEq_one 2 3 5 (by decide)
      push_cast at this; rw [this]; exact_mod_cast h25

    have h85 : dedekindSum ((8 : ℕ) : ℤ) 5 = 0 := by
      rw [show ((8 : ℕ) : ℤ) = 3 + 1 * (5 : ℕ) by norm_num, dedekindSum_add_mul]; exact h35
    have hrec58 := dedekindSum_add_dedekindSum 5 8 (by norm_num) (by norm_num) (by norm_num)
    have h58 : dedekindSum 5 8 = -(1 / 16) := by rw [h85] at hrec58; push_cast at hrec58 ⊢; linarith

    have hper : dedekindSum ((120 * j + 61 : ℕ) : ℤ) 8 = dedekindSum 5 8 := by
      rw [← dedekindSum_add_mul 5 (15 * j + 7) 8]
      congr 1
      push_cast
      ring
    have hcop : Nat.Coprime 8 (120 * j + 61) :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr ⟨60 * j + 30, by ring⟩)
    have hrec := dedekindSum_add_dedekindSum 8 (120 * j + 61) (by norm_num) (by positivity) hcop
    have h81 : dedekindSum 8 1 = 0 := dedekindSum_one_right 8
    have hs : dedekindSum 8 (120 * j + 61) = ((8 : ℚ) / ((120 * j + 61 : ℕ) : ℚ) + ((120 * j + 61 : ℕ) : ℚ) / 8
        + 1 / ((8 : ℚ) * ((120 * j + 61 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 16 := by
      have h := hrec
      rw [hper, h58] at h
      push_cast at h ⊢
      linarith
    rw [h81, hs, hgcd]
    have hne : ((120 * j + 61 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [hgcd, show Int.natAbs (-(5 * (j : ℤ) + 3)) = 5 * j + 3 by omega,
      show ((120 * j + 61) - 1) / 12 = 10 * j + 5 by omega]
    exact Nat.isCoprime_iff_coprime.mp ⟨2, -1, by push_cast; ring⟩

end S_rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne
end P2MW
export P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne (solution)
