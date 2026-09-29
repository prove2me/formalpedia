-- Prove2me | solution 1 for mme_stothers_phi233_asymptotic_completion_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:10:11.023553+00:00
-- url     : https://prove2.me/submissions/45925179-e6db-4c36-b5e9-8d35267d2066

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_integer_profile_rounding
import Theorems.Thm_mme_stothers_phi233_rounded_tail_completion_ratio

open MME Filter

set_option autoImplicit false
set_option warningAsError true

/-- End-to-end analytic bridge for the exceptional `phi_233` count: every
positive stationary real profile has exact integral approximants whose
same-marginal ambiguity is subexponential. -/
theorem solution
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hsigmaUpper : 2 * a + b < 2 / 3)
    (hmuUpper : a + c < 1 / 2) :
    ∃ A B C D : ℕ → ℕ, ∃ k : ℕ,
      (∀ n, 2 * A n + B n + C n + D n = n) ∧
      Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b) ∧
      Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d) ∧
      0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (Nat.card
              (MME.StothersFourth.Phi233.MarginalAddress
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))) : ℝ) ≤
            (((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
              Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
              (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10 *
              (Nat.card
                (MME.StothersFourth.Phi233.ExactProfileAddress
                  (n + k) (A (n + k)) (B (n + k))
                  (C (n + k)) (D (n + k))) : ℝ) := by
  obtain ⟨A, B, C, D, hsum, hA, hB, hC, hD⟩ :=
    mme_stothers_phi233_exact_integer_profile_rounding
      a b c d ha.le hb.le hc.le hd.le htotal
  obtain ⟨k, hk, hratio⟩ :=
    mme_stothers_phi233_rounded_tail_completion_ratio
      A B C D a b c d hsum ha hb hc hd htotal hstation
      hsigmaUpper hmuUpper hA hB hC hD
  exact ⟨A, B, C, D, k, hsum, hA, hB, hC, hD, hk, hratio⟩
