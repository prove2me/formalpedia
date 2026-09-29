-- Prove2me | solution 1 for mme_prime_behrend_dominates_bounded_collision_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:21:38.929098+00:00
-- url     : https://prove2.me/submissions/4e6b9dad-5c25-4731-9372-0633bf2d3856

import Theorems.Thm_mme_behrend_bounded_degree_scale
import Theorems.Thm_mme_prime_half_modulus_behrend

set_option autoImplicit false

/-- A prime-modulus progression-free set whose cardinality pays six times any
degree bounded by `5^N`, with an explicit square-root-exponential modulus. -/
theorem solution (N D : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) :
    ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (6 * D : ℝ) ≤ (S.card : ℝ) ∧
        (p : ℝ) ≤ (D : ℝ) *
          Real.exp (2000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let Q : ℕ := Nat.ceil ((D : ℝ) * Real.exp (1000 * r))
  have hscale := mme_behrend_bounded_degree_scale N D hD1 hD5
  change 0 < Q ∧
      (6 * D : ℝ) ≤
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ∧
      (4 * Q : ℝ) ≤ (D : ℝ) * Real.exp (2000 * r) at hscale
  obtain ⟨hQ, hQcard, hQrate⟩ := hscale
  obtain ⟨p, hp, hp_lower, hp_upper, S, hSrange, hSfree, hScard⟩ :=
    mme_prime_half_modulus_behrend Q hQ
  have hr : 1 ≤ r := by
    change 1 ≤ Real.sqrt (((N + 1 : ℕ) : ℝ))
    rw [Real.one_le_sqrt]
    norm_num
  have he : (2 : ℝ) ≤ Real.exp (1000 * r) := by
    calc
      (2 : ℝ) ≤ 1000 * r + 1 := by nlinarith
      _ ≤ Real.exp (1000 * r) := Real.add_one_le_exp _
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hx2 : (2 : ℝ) ≤ (D : ℝ) * Real.exp (1000 * r) := by
    nlinarith [mul_le_mul hd he (by norm_num) (by positivity)]
  have hxQ :
      (D : ℝ) * Real.exp (1000 * r) ≤ (Q : ℝ) := by
    simpa only [Q] using
      Nat.le_ceil ((D : ℝ) * Real.exp (1000 * r))
  have hQ2 : 2 ≤ Q := by
    exact_mod_cast hx2.trans hxQ
  have hp5 : 5 ≤ p := by omega
  have hcard : (6 * D : ℝ) ≤ (S.card : ℝ) := hQcard.trans hScard
  have hprate :
      (p : ℝ) ≤ (D : ℝ) * Real.exp (2000 * r) := by
    calc
      (p : ℝ) ≤ (4 : ℝ) * (Q : ℝ) := by exact_mod_cast hp_upper
      _ ≤ (D : ℝ) * Real.exp (2000 * r) := hQrate
  refine ⟨p, hp, hp5, S, hSrange, hSfree, hcard, ?_⟩
  simpa only [r] using hprate
