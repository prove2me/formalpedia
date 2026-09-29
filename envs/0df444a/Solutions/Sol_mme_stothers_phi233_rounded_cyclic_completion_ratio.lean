-- Prove2me | solution 1 for mme_stothers_phi233_rounded_cyclic_completion_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:26:28.473493+00:00
-- url     : https://prove2.me/submissions/977149cf-a8b1-4a08-8baa-40a2cc3615ec

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_rounded_tail_completion_ratio
import Theorems.Thm_mme_stothers_phi233_cyclic_cardinality_ratio

open MME Filter

set_option autoImplicit false
set_option warningAsError true

/-- The one-coordinate subexponential completion bound, cubed into the
actual cyclic ambient and target finsets used by type-2 hashing. -/
theorem solution
    (A B C D : ℕ → ℕ) (a b c d : ℝ)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hsigmaUpper : 2 * a + b < 2 / 3)
    (hmuUpper : a + c < 1 / 2)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    ∃ k : ℕ, 0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          ((MME.StothersFourth.Phi233.ambientFinset
              (n + k) (A (n + k)) (B (n + k))
              (C (n + k)) (D (n + k))).card : ℝ) ≤
            ((((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
                Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
                (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10) ^ 3 *
              ((MME.StothersFourth.Phi233.targetFinset
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))).card : ℝ) := by
  obtain ⟨k, hk, hratio⟩ :=
    mme_stothers_phi233_rounded_tail_completion_ratio
      A B C D a b c d hsum ha hb hc hd htotal hstation
      hsigmaUpper hmuUpper hA hB hC hD
  refine ⟨k, hk, ?_⟩
  intro ε hε
  filter_upwards [hratio ε hε] with n hn
  exact mme_stothers_phi233_cyclic_cardinality_ratio
    (n + k) (A (n + k)) (B (n + k))
    (C (n + k)) (D (n + k)) _ hn
