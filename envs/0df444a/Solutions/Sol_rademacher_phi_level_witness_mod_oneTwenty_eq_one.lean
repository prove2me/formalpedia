-- Prove2me | solution 1 for rademacher_phi_level_witness_mod_oneTwenty_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/50905a59-7e40-54c9-848a-e47b73b83704

import Definitions.Def_NumberTheory_DedekindSum
import Theorems.Thm_dedekindSum_add_dedekindSum
import Theorems.Thm_dedekindSum_one_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_one

set_option autoImplicit false

namespace WNF1E

private lemma sval_two (u : ℕ) :
    dedekindSum 2 (2 * u + 1) = (2 * (u : ℚ)) * (2 * (u : ℚ) - 4) / (24 * (2 * (u : ℚ) + 1)) := by
  have hco : Nat.Coprime 2 (2 * u + 1) := by
    rw [Nat.coprime_comm]
    unfold Nat.Coprime
    rw [show 2 * u + 1 = 1 + u * 2 from by ring, Nat.gcd_add_mul_right_left]
    decide
  have hrec := dedekindSum_add_dedekindSum 2 (2 * u + 1) (by norm_num) (by omega) hco
  have h12 : dedekindSum ((2 * u + 1 : ℕ) : ℤ) 2 = 0 := by
    rw [show ((2 * u + 1 : ℕ) : ℤ) = 1 + (u : ℤ) * ((2 : ℕ) : ℤ) from by push_cast; ring,
      dedekindSum_add_mul, dedekindSum_one_left]
    norm_num
  rw [h12, add_zero] at hrec
  have h2 : dedekindSum 2 (2 * u + 1)
      = ((2 : ℚ) / (2 * (u : ℚ) + 1) + (2 * (u : ℚ) + 1) / 2 + 1 / (2 * (2 * (u : ℚ) + 1))) / 12
          - 1 / 4 := by
    exact_mod_cast hrec
  rw [h2]
  have hK : (2 * (u : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem etaPhase_witness_mod120_1 (w t : ℕ) :
    12 * (((-((60 * 2 ^ w * (2 * t + 1) + 15 * t + 8 : ℕ) : ℤ) + 2 ^ (w + 4) : ℤ) : ℚ)
            * (1 - ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ))
            / (12 * ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ))
          + dedekindSum (2 ^ (w + 4)) 1 - dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1))
        = ((Nat.gcd ((120 * 2 ^ w * (2 * t + 1) + 1) - 1) 12 : ℕ) : ℚ) * (2 ^ (w + 1) * (5 * (t : ℤ) + 2)) ∧
      Nat.Coprime (5 * t + 2) (5 * (2 * t + 1)) := by
  have hgcd : Nat.gcd ((120 * 2 ^ w * (2 * t + 1) + 1) - 1) 12 = 12 := by
    rw [Nat.add_sub_cancel, show 120 * 2 ^ w * (2 * t + 1) = (10 * 2 ^ w * (2 * t + 1)) * 12 from by ring,
      Nat.gcd_mul_left_left]
  constructor
  ·
    have h2L : Nat.Coprime 2 (120 * 2 ^ w * (2 * t + 1) + 1) := by
      rw [Nat.coprime_comm]
      unfold Nat.Coprime
      rw [show 120 * 2 ^ w * (2 * t + 1) + 1 = 1 + (60 * 2 ^ w * (2 * t + 1)) * 2 from by ring,
        Nat.gcd_add_mul_right_left]
      decide
    have hco1 : Nat.Coprime (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1) := Nat.Coprime.pow_left _ h2L
    have hK2 : Nat.Coprime (8 * 2 ^ w + 1) 2 := by
      unfold Nat.Coprime
      rw [show 8 * 2 ^ w + 1 = 1 + (4 * 2 ^ w) * 2 from by ring, Nat.gcd_add_mul_right_left]
      decide
    have hco2 : Nat.Coprime (8 * 2 ^ w + 1) (2 ^ (w + 4)) := Nat.Coprime.pow_right _ hK2

    have hrec1 := dedekindSum_add_dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1)
      (by positivity) (by positivity) hco1
    have hL16 : dedekindSum ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℤ) (2 ^ (w + 4))
        = dedekindSum ((8 * 2 ^ w + 1 : ℕ) : ℤ) (2 ^ (w + 4)) := by
      rw [show ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℤ)
          = ((8 * 2 ^ w + 1 : ℕ) : ℤ) + (15 * (t : ℤ) + 7) * ((2 ^ (w + 4) : ℕ) : ℤ) from by push_cast; ring,
        dedekindSum_add_mul]
    rw [hL16] at hrec1

    have hrec2 := dedekindSum_add_dedekindSum (8 * 2 ^ w + 1) (2 ^ (w + 4)) (by positivity) (by positivity) hco2
    have h16K : dedekindSum ((2 ^ (w + 4) : ℕ) : ℤ) (8 * 2 ^ w + 1) = -dedekindSum 2 (8 * 2 ^ w + 1) := by
      rw [show ((2 ^ (w + 4) : ℕ) : ℤ) = -2 + 2 * ((8 * 2 ^ w + 1 : ℕ) : ℤ) from by push_cast; ring,
        dedekindSum_add_mul, show (-2 : ℤ) = -(2 : ℤ) from rfl, dedekindSum_neg]
    rw [h16K] at hrec2

    have h7 : dedekindSum 2 (8 * 2 ^ w + 1)
        = (2 * (4 * (2 : ℚ) ^ w)) * (2 * (4 * (2 : ℚ) ^ w) - 4) / (24 * (2 * (4 * (2 : ℚ) ^ w) + 1)) := by
      rw [show 8 * 2 ^ w + 1 = 2 * (4 * 2 ^ w) + 1 from by ring, sval_two]
      push_cast
      ring

    have hX : (0 : ℚ) < (2 : ℚ) ^ w := by positivity
    have hLq : (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1) ≠ 0 := by positivity
    have hKq : (8 * (2 : ℚ) ^ w + 1) ≠ 0 := by positivity
    have hDq : ((2 : ℚ) ^ (w + 4)) ≠ 0 := by positivity
    have e1 : dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1)
          + dedekindSum (8 * 2 ^ w + 1) (2 ^ (w + 4))
        = (((2 : ℚ) ^ (w + 4)) / (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1)
            + (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1) / ((2 : ℚ) ^ (w + 4))
            + 1 / (((2 : ℚ) ^ (w + 4)) * (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1))) / 12 - 1 / 4 := by
      exact_mod_cast hrec1
    have e2 : dedekindSum (8 * 2 ^ w + 1) (2 ^ (w + 4)) + -dedekindSum 2 (8 * 2 ^ w + 1)
        = ((8 * (2 : ℚ) ^ w + 1) / ((2 : ℚ) ^ (w + 4)) + ((2 : ℚ) ^ (w + 4)) / (8 * (2 : ℚ) ^ w + 1)
            + 1 / ((8 * (2 : ℚ) ^ w + 1) * ((2 : ℚ) ^ (w + 4)))) / 12 - 1 / 4 := by
      exact_mod_cast hrec2
    have hS : dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1)
        = ((((2 : ℚ) ^ (w + 4)) / (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1)
            + (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1) / ((2 : ℚ) ^ (w + 4))
            + 1 / (((2 : ℚ) ^ (w + 4)) * (120 * (2 : ℚ) ^ w * (2 * (t : ℚ) + 1) + 1))) / 12 - 1 / 4)
          - (((8 * (2 : ℚ) ^ w + 1) / ((2 : ℚ) ^ (w + 4)) + ((2 : ℚ) ^ (w + 4)) / (8 * (2 : ℚ) ^ w + 1)
            + 1 / ((8 * (2 : ℚ) ^ w + 1) * ((2 : ℚ) ^ (w + 4)))) / 12 - 1 / 4)
          - (2 * (4 * (2 : ℚ) ^ w)) * (2 * (4 * (2 : ℚ) ^ w) - 4) / (24 * (2 * (4 * (2 : ℚ) ^ w) + 1)) := by
      linarith [e1, e2, h7]
    rw [dedekindSum_one_right, hgcd, hS]
    push_cast
    have hpow4 : (2 : ℚ) ^ (w + 4) = 16 * (2 : ℚ) ^ w := by rw [pow_add]; norm_num; ring
    have hpow1 : (2 : ℚ) ^ (w + 1) = 2 * (2 : ℚ) ^ w := by rw [pow_add]; norm_num; ring
    rw [hpow4, hpow1]
    have hKq' : (2 * (4 * (2 : ℚ) ^ w) + 1) ≠ 0 := by positivity
    have h16X : (16 * (2 : ℚ) ^ w) ≠ 0 := by positivity
    field_simp
    ring
  ·
    have ha := Nat.gcd_dvd_left (5 * t + 2) (5 * (2 * t + 1))
    have hb := Nat.gcd_dvd_right (5 * t + 2) (5 * (2 * t + 1))
    have h1 : Nat.gcd (5 * t + 2) (5 * (2 * t + 1)) ∣ 1 := by
      have h3 := Nat.dvd_sub hb (Dvd.dvd.mul_left ha 2)
      rwa [show 5 * (2 * t + 1) - 2 * (5 * t + 2) = 1 from by omega] at h3
    exact Nat.dvd_one.mp h1

end WNF1E

theorem solution (w t : ℕ) : 12 * (((-((60 * 2 ^ w * (2 * t + 1) + 15 * t + 8 : ℕ) : ℤ) + 2 ^ (w + 4) : ℤ) : ℚ) * (1 - ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ)) / (12 * ((120 * 2 ^ w * (2 * t + 1) + 1 : ℕ) : ℚ)) + dedekindSum (2 ^ (w + 4)) 1 - dedekindSum (2 ^ (w + 4)) (120 * 2 ^ w * (2 * t + 1) + 1)) = ((Nat.gcd ((120 * 2 ^ w * (2 * t + 1) + 1) - 1) 12 : ℕ) : ℚ) * (2 ^ (w + 1) * (5 * (t : ℤ) + 2)) ∧ Nat.Coprime (5 * t + 2) (5 * (2 * t + 1)) :=
  WNF1E.etaPhase_witness_mod120_1 w t

end S_rademacher_phi_level_witness_mod_oneTwenty_eq_one
end P2MW
export P2MW.S_rademacher_phi_level_witness_mod_oneTwenty_eq_one (solution)
