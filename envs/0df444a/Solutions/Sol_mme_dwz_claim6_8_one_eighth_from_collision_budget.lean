-- Prove2me | solution 1 for mme_dwz_claim6_8_one_eighth_from_collision_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:08:52.724096+00:00
-- url     : https://prove2.me/submissions/570d1ffb-242c-4cf4-9ee5-f3edf4c369d5

import Mathlib
import Theorems.Thm_mme_dwz_claim6_8_collision_union_bound

set_option autoImplicit false

/-!
The exact cardinal form of the final one-eighth step in DWZ Claim 6.8.
The collision theorem supplies one fiber of density at most `1 / M` per
compatible competitor.  When the modulus is at least eight times the number
of competitors, at most one eighth of the conditioned parameter space is bad.
-/

theorem solution
    {Ω A : Type}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq A]
    (candidates : Finset A)
    (compatible : A → Prop) [DecidablePred compatible]
    (collides : A → Ω → Prop) [∀ a, DecidablePred (collides a)]
    (bad : Ω → Prop) [DecidablePred bad]
    (M : ℕ) (hM : 0 < M)
    (hbad : ∀ ω, bad ω →
      ∃ a ∈ candidates, compatible a ∧ collides a ω)
    (hcollision : ∀ a ∈ candidates, compatible a →
      M * (Finset.univ.filter (collides a)).card ≤ Fintype.card Ω)
    (hbudget : 8 * (candidates.filter compatible).card ≤ M) :
    8 * (Finset.univ.filter bad).card ≤ Fintype.card Ω := by
  let C := (candidates.filter compatible).card
  let B := (Finset.univ.filter bad).card
  let O := Fintype.card Ω
  have hunion : M * B ≤ C * O :=
    mme_dwz_claim6_8_collision_union_bound
      candidates compatible collides bad M hbad hcollision
  by_cases hC : C = 0
  · have hMB : M * B = 0 := Nat.eq_zero_of_le_zero (by simpa [hC] using hunion)
    have hB : B = 0 := by
      rcases Nat.mul_eq_zero.mp hMB with hMzero | hBzero
      · exact (Nat.ne_of_gt hM hMzero).elim
      · exact hBzero
    simp [B, hB]
  · have hCpos : 0 < C := Nat.pos_of_ne_zero hC
    have hscaled : C * (8 * B) ≤ C * O := by
      calc
        C * (8 * B) = (8 * C) * B := by ring
        _ ≤ M * B := Nat.mul_le_mul_right B hbudget
        _ ≤ C * O := hunion
    exact Nat.le_of_mul_le_mul_left hscaled hCpos
