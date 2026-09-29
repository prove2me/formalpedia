-- Prove2me | solution 1 for talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T17:08:24.286743+00:00
-- url     : https://prove2.me/submissions/cdfe26a0-2a8f-4ea5-8da3-0f859a2cd1d2

import Theorems.Thm_finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
import Theorems.Thm_talagrand_bernoulli_sSup_log_tail_from_finite_max

open MatrixCompletion
open scoped Classical BigOperators

/-!
Source: Candès--Recht, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations
(9.1)--(9.2).

This sketch decomposes the generic Appendix 9.1 Lean node into the two
mathematical issues that are actually present.

First, the finite-class theorem is the genuine Bousquet--Talagrand empirical
process concentration inequality: for a finite symmetric class of centered
Bernoulli coordinate sums, the maximum satisfies the logarithmic tail from
equation (9.2).

Second, the `sSup` bridge is formal Lean bookkeeping.  The paper states the
theorem for a countable class, while this node allows an arbitrary index type.
Because the Bernoulli observation set has finite state space, the arbitrary
`sSup` process is obtained as a limit of finite symmetric subfamilies.

No Candes--Recht matrix-completion geometry is hidden here; this is exactly the
probabilistic theorem cited before applying it to the tangent-sampling
supremum.
-/

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) (Z : Finset (Fin n₁ × Fin n₂) → ℝ)
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ Omega,
          Z Omega =
            sSup {v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) -
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      coeff a i j)}) →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Z Omega -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z))) := by
  exact
    talagrand_bernoulli_sSup_log_tail_from_finite_max
      finite_max_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
