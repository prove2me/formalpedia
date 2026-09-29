-- Prove2me | solution 1 for mme_stothers_phi233_stationary_completion_ratio_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:53:13.759064+00:00
-- url     : https://prove2.me/submissions/a2f1cc5b-8e5a-4a9d-8ea1-da6ab8171af4

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_stationary_marginal_address_entropy_upper

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- For an exact positive stationary integer profile, the full `phi_233`
same-marginal family is only polynomially larger than its target-profile
subfamily. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hN : 0 < N) (haN : 0 < alpha) (hbN : 0 < beta)
    (hcN : 0 < gamma) (hdN : 0 < delta)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (hsigmaUpper :
      ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) < 2 / 3)
    (hmuUpper :
      ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) < 1 / 2)
    (hcritical : alpha ^ (2 : ℕ) * delta =
      beta ^ (2 : ℕ) * gamma) :
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
      ((((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10) *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) := by
  let a : ℝ := (alpha : ℝ) / (N : ℝ)
  let b : ℝ := (beta : ℝ) / (N : ℝ)
  let c : ℝ := (gamma : ℝ) / (N : ℝ)
  let d : ℝ := (delta : ℝ) / (N : ℝ)
  let sigma : ℝ := ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ)
  let mu : ℝ := ((alpha + gamma : ℕ) : ℝ) / (N : ℝ)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hsigma0 : 0 < sigma := by
    dsimp only [sigma]
    positivity
  have hmu0 : 0 < mu := by
    dsimp only [mu]
    positivity
  have hsumR :
      2 * (alpha : ℝ) + beta + gamma + delta = (N : ℝ) := by
    exact_mod_cast hsum
  have htotal : 2 * a + b + c + d = 1 := by
    dsimp only [a, b, c, d]
    field_simp [hNR]
    linarith
  have hab : 2 * a + b = sigma := by
    dsimp only [a, b, sigma]
    push_cast
    ring
  have hac : a + c = mu := by
    dsimp only [a, c, mu]
    push_cast
    ring
  have hcriticalR :
      (alpha : ℝ) ^ (2 : ℕ) * delta =
        (beta : ℝ) ^ (2 : ℕ) * gamma := by
    exact_mod_cast hcritical
  have hcriticalProfile : a ^ (2 : ℕ) * d = b ^ (2 : ℕ) * c := by
    dsimp only [a, b, c, d]
    field_simp [hNR]
    exact hcriticalR
  have hstation :=
    mme_stothers_phi233_log_stationarity_of_critical_product
      a b c d ha hb hc hd hcriticalProfile
  have hAmbient :=
    mme_stothers_phi233_stationary_marginal_address_entropy_upper
      N alpha beta gamma delta hN sigma mu a b c d
      hsigma0 (by simpa only [sigma] using hsigmaUpper)
      hmu0 (by simpa only [mu] using hmuUpper)
      (by rfl) (by rfl) ha hb hc hd htotal hab hac hstation
  have hExact :=
    mme_stothers_phi233_exact_profile_entropy_polynomial_lower
      N alpha beta gamma delta hN hsum
  have haHalf : a / 2 =
      (alpha : ℝ) / ((2 * N : ℕ) : ℝ) := by
    dsimp only [a]
    push_cast
    ring
  have hbHalf : b / 2 =
      (beta : ℝ) / ((2 * N : ℕ) : ℝ) := by
    dsimp only [b]
    push_cast
    ring
  have hcHalf : c / 2 =
      (gamma : ℝ) / ((2 * N : ℕ) : ℝ) := by
    dsimp only [c]
    push_cast
    ring
  have hdHalf : d / 2 =
      (delta : ℝ) / ((2 * N : ℕ) : ℝ) := by
    dsimp only [d]
    push_cast
    ring
  rw [haHalf, hbHalf, hcHalf, hdHalf] at hAmbient
  calc
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
        (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N : ℕ) : ℝ) *
            (4 * Real.negMulLog ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
              2 * Real.negMulLog ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
              2 * Real.negMulLog ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
              2 * Real.negMulLog ((delta : ℝ) / ((2 * N : ℕ) : ℝ)))) :=
      hAmbient
    _ ≤ (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        ((6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10 *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hExact (by positivity)
    _ = ((((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10) *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) := by ring
