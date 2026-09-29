-- Prove2me | solution 1 for mme_stothers_phi233_integer_histogram_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:16:01.3168+00:00
-- url     : https://prove2.me/submissions/4afc5e03-ff41-46e6-bc71-05bc6a3d7070

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma : ℕ) (hN : 0 < N)
    (w : Fin 10 → ℕ)
    (htotal : ∑ r : Fin 10, w r = 2 * N)
    (hsigma0 : w 0 + w 1 + w 2 = 2 * alpha + beta)
    (hsigma2 : w 7 + w 8 + w 9 = 2 * alpha + beta)
    (hmuJ0 : w 3 + w 7 = alpha + gamma)
    (hmuJ3 : w 2 + w 6 = alpha + gamma)
    (hmuK0 : w 6 + w 9 = alpha + gamma)
    (hmuK3 : w 0 + w 3 = alpha + gamma) :
    let p : Fin 10 → ℝ := fun r ↦ (w r : ℝ) / (2 * N : ℕ)
    let sigma : ℝ := (2 * alpha + beta : ℕ) / (N : ℝ)
    let mu : ℝ := (alpha + gamma : ℕ) / (N : ℝ)
    (∀ r, 0 ≤ p r) ∧
      (∑ r : Fin 10, p r) = 1 ∧
      p 0 + p 1 + p 2 = sigma / 2 ∧
      p 7 + p 8 + p 9 = sigma / 2 ∧
      p 3 + p 7 = mu / 2 ∧
      p 2 + p 6 = mu / 2 ∧
      p 6 + p 9 = mu / 2 ∧
      p 0 + p 3 = mu / 2 := by
  dsimp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h2NR : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by norm_num
  have htotalR : (∑ r : Fin 10, (w r : ℝ)) = 2 * (N : ℝ) := by
    exact_mod_cast htotal
  have hsigma0R :
      (w 0 : ℝ) + w 1 + w 2 = 2 * (alpha : ℝ) + beta := by
    exact_mod_cast hsigma0
  have hsigma2R :
      (w 7 : ℝ) + w 8 + w 9 = 2 * (alpha : ℝ) + beta := by
    exact_mod_cast hsigma2
  have hmuJ0R : (w 3 : ℝ) + w 7 = alpha + gamma := by
    exact_mod_cast hmuJ0
  have hmuJ3R : (w 2 : ℝ) + w 6 = alpha + gamma := by
    exact_mod_cast hmuJ3
  have hmuK0R : (w 6 : ℝ) + w 9 = alpha + gamma := by
    exact_mod_cast hmuK0
  have hmuK3R : (w 0 : ℝ) + w 3 = alpha + gamma := by
    exact_mod_cast hmuK3
  constructor
  · intro r
    positivity
  constructor
  · rw [← Finset.sum_div]
    rw [h2NR, htotalR]
    field_simp
  constructor
  · rw [h2NR]
    push_cast
    field_simp
    linarith
  constructor
  · rw [h2NR]
    push_cast
    field_simp
    linarith
  constructor
  · rw [h2NR]
    push_cast
    field_simp
    linarith
  constructor
  · rw [h2NR]
    push_cast
    field_simp
    linarith
  constructor
  · rw [h2NR]
    push_cast
    field_simp
    linarith
  · rw [h2NR]
    push_cast
    field_simp
    linarith
