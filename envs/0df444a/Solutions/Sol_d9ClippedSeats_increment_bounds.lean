-- Prove2me | solution 1 for d9ClippedSeats_increment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:26:54.067022+00:00
-- url     : https://prove2.me/submissions/c3a57d2c-d023-47d6-8ac4-df7b7e6d9060

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ d9ClippedSeats p x t - d9ClippedSeats p x s ∧
      d9ClippedSeats p x t - d9ClippedSeats p x s ≤ t - s := by
  let c : ℝ → ℝ := fun z => d9ClippedSeats p x z
  have hbelow (z : ℝ) (hz : z ≤ p) : c z = 0 := by
    dsimp [c, d9ClippedSeats]
    simp [max_eq_left (sub_nonpos.mpr hz), min_eq_right hx]
  have hmiddle (z : ℝ) (hz₁ : p ≤ z) (hz₂ : z ≤ p + x) :
      c z = z - p := by
    dsimp [c, d9ClippedSeats]
    simp [max_eq_right (sub_nonneg.mpr hz₁),
      min_eq_right (by linarith : z - p ≤ x)]
  have habove (z : ℝ) (hz : p + x ≤ z) : c z = x := by
    dsimp [c, d9ClippedSeats]
    have hpz : p ≤ z := by linarith
    simp [max_eq_right (sub_nonneg.mpr hpz),
      min_eq_left (by linarith : x ≤ z - p)]
  change 0 ≤ c t - c s ∧ c t - c s ≤ t - s
  by_cases hsp : s < p
  · by_cases htp : t < p
    · rw [hbelow s (le_of_lt hsp), hbelow t (le_of_lt htp)]
      constructor <;> simp <;> linarith
    · have hpt : p ≤ t := le_of_not_gt htp
      by_cases htu : t < p + x
      · rw [hbelow s (le_of_lt hsp), hmiddle t hpt (le_of_lt htu)]
        constructor <;> linarith
      · have hcap : p + x ≤ t := le_of_not_gt htu
        rw [hbelow s (le_of_lt hsp), habove t hcap]
        constructor <;> simp <;> linarith
  · have hps : p ≤ s := le_of_not_gt hsp
    by_cases hsu : s < p + x
    · by_cases htu : t < p + x
      · have hpt : p ≤ t := le_trans hps hst
        rw [hmiddle s hps (le_of_lt hsu), hmiddle t hpt (le_of_lt htu)]
        constructor <;> linarith
      · have hcap : p + x ≤ t := le_of_not_gt htu
        rw [hmiddle s hps (le_of_lt hsu), habove t hcap]
        constructor <;> linarith
    · have hcaps : p + x ≤ s := le_of_not_gt hsu
      have hcapt : p + x ≤ t := le_trans hcaps hst
      rw [habove s hcaps, habove t hcapt]
      constructor <;> simp <;> linarith
