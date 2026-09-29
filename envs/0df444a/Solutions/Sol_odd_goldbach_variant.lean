-- Prove2me | solution 1 for odd_goldbach_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:28:56.806248+00:00
-- url     : https://prove2.me/submissions/eb5cefee-f04a-4127-b0ad-2899141e8567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_goldbach_odd_variant

theorem solution :
    ∀ n : ℕ, 7 ≤ n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      n = p + q + r ∧ p ≤ q ∧ q ≤ r := by
  intro n hn hnot
  by_cases h7 : n = 7
  · subst n
    exact ⟨2, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩
  · have hn7 : 7 < n := by omega
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      goldbach_odd_variant n hn7 hnot
    by_cases hpq : p ≤ q
    · by_cases hqr : q ≤ r
      · exact ⟨p, q, r, hp, hq, hr, hsum, hpq, hqr⟩
      · have hrq : r ≤ q := by omega
        by_cases hpr : p ≤ r
        · exact ⟨p, r, q, hp, hr, hq, by omega, hpr, hrq⟩
        · have hrp : r ≤ p := by omega
          exact ⟨r, p, q, hr, hp, hq, by omega, hrp, hpq⟩
    · have hqp : q ≤ p := by omega
      by_cases hpr : p ≤ r
      · exact ⟨q, p, r, hq, hp, hr, by omega, hqp, hpr⟩
      · have hrp : r ≤ p := by omega
        by_cases hqr : q ≤ r
        · exact ⟨q, r, p, hq, hr, hp, by omega, hqr, hrp⟩
        · have hrq : r ≤ q := by omega
          exact ⟨r, q, p, hr, hq, hp, by omega, hrq, hqp⟩
