-- Prove2me | solution 1 for mme_stothers_phi233_stationary_profile_sequence_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:01:02.790799+00:00
-- url     : https://prove2.me/submissions/af9df5c0-ef11-4432-8655-c0151ce82f35

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_positive_critical_profile_exists

set_option autoImplicit false
set_option warningAsError true

/-- Pointwise interior marginal data have a coherent sequence of positive
critical `phi_233` profiles. -/
theorem solution
    (sigma mu : ℕ → ℝ)
    (hsigma0 : ∀ n, 0 < sigma n)
    (hmu0 : ∀ n, 0 < mu n)
    (hsigma1 : ∀ n, sigma n < 1)
    (hcompat : ∀ n, sigma n / 2 + mu n < 1) :
    ∃ A B C D : ℕ → ℝ,
      (∀ n, 0 < A n) ∧ (∀ n, 0 < B n) ∧
      (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
      (∀ n, 2 * A n + B n + C n + D n = 1) ∧
      (∀ n, 2 * A n + B n = sigma n) ∧
      (∀ n, A n + C n = mu n) ∧
      (∀ n, (A n) ^ (2 : ℕ) * D n = (B n) ^ (2 : ℕ) * C n) := by
  classical
  have hexists : ∀ n : ℕ, ∃ x : ℝ × ℝ × ℝ × ℝ,
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
      2 * x.1 + x.2.1 + x.2.2.1 + x.2.2.2 = 1 ∧
      2 * x.1 + x.2.1 = sigma n ∧ x.1 + x.2.2.1 = mu n ∧
      x.1 ^ (2 : ℕ) * x.2.2.2 = x.2.1 ^ (2 : ℕ) * x.2.2.1 := by
    intro n
    obtain ⟨a, b, c, d, ha, hb, hc, hd, htotal, hab, hac, hcritical⟩ :=
      mme_stothers_phi233_positive_critical_profile_exists
        (sigma n) (mu n) (hsigma0 n) (hmu0 n) (hsigma1 n) (hcompat n)
    exact ⟨(a, b, c, d), ha, hb, hc, hd, htotal, hab, hac, hcritical⟩
  let profile : ℕ → ℝ × ℝ × ℝ × ℝ := fun n ↦ Classical.choose (hexists n)
  refine ⟨fun n ↦ (profile n).1, fun n ↦ (profile n).2.1,
    fun n ↦ (profile n).2.2.1, fun n ↦ (profile n).2.2.2, ?_⟩
  have hprofile := fun n ↦ Classical.choose_spec (hexists n)
  exact ⟨fun n ↦ (hprofile n).1,
    fun n ↦ (hprofile n).2.1,
    fun n ↦ (hprofile n).2.2.1,
    fun n ↦ (hprofile n).2.2.2.1,
    fun n ↦ (hprofile n).2.2.2.2.1,
    fun n ↦ (hprofile n).2.2.2.2.2.1,
    fun n ↦ (hprofile n).2.2.2.2.2.2.1,
    fun n ↦ (hprofile n).2.2.2.2.2.2.2⟩
