-- Prove2me | solution 1 for mme_dwz_finite_candidate_family_common_prime_with_exponential_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:17:18.035739+00:00
-- url     : https://prove2.me/submissions/eb19e304-eef7-4d11-8d71-20793a4fd8a5

import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap
import Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (L d : ℕ) (R : ℝ)
    (candidates : Outer → Block → Finset Outer)
    (hd : d ≤ 15 ^ L)
    (hOuter : Fintype.card Outer ≤ 15 ^ L)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ Q p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ Q) ∧
      Q ≤ Fintype.card Outer ∧
      Q ≤ 15 ^ L ∧
      (Q : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d Q) < p ∧
      p ≤ 2 * max 4 (8 * max d Q) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
      (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  obtain ⟨Q, p, hcandidate, hQOuter, hQR, hp, hpOdd, hpFour,
    hpd, hpcandidate, hpLower, hpUpper, hpRate⟩ :=
    mme_dwz_finite_candidate_family_common_prime_with_card_cap
      candidates d R hR
  have hQPow : Q ≤ 15 ^ L := hQOuter.trans hOuter
  have hpExp :=
    mme_dwz_common_prime_le_exp_sixteen_length L d Q p hd hQPow hpUpper
  exact ⟨Q, p, hcandidate, hQOuter, hQPow, hQR, hp, hpOdd, hpFour,
    hpd, hpcandidate, hpLower, hpUpper, hpRate, hpExp⟩
