-- Prove2me | Theorems.Thm_Erdos287_weighted_cauchy_fixed_auxiliary_modulus
-- name    : Erdos287.weighted_cauchy_fixed_auxiliary_modulus
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T19:02:52.376464+00:00
-- url     : https://prove2.me/theorems/7fbf4b2c-feb0-4e96-a7cb-7ed967e0ea4a
-- title:
--   Weighted Cauchy–Schwarz with the auxiliary modulus fixed in each square
-- statement:
--   Let $Q$ be a finite set of positive integers and $I$ a finite set. For real arrays $\gamma_q,\alpha_i,E_{q,i}$, the square of $\sum_{q,i}\gamma_q\alpha_iE_{q,i}$ is at most $(\sum_q\gamma_q^2/q)(\sum_i\alpha_i^2)(\sum_{q,i} qE_{q,i}^2)$.
-- source:
--   Erdős #287, harmonic weighting in mixed Type II dispersion.

import Mathlib

theorem Erdos287.weighted_cauchy_fixed_auxiliary_modulus {ι : Type*} (Q : Finset ℕ) (I : Finset ι)
    (hQ : ∀ q ∈ Q, 0 < q) (γ : ℕ → ℝ) (α : ι → ℝ) (E : ℕ → ι → ℝ) :
    (∑ q ∈ Q, γ q * ∑ i ∈ I, α i * E q i) ^ 2 ≤
      (∑ q ∈ Q, (γ q) ^ 2 / (q : ℝ)) * (∑ i ∈ I, (α i) ^ 2) *
        ∑ q ∈ Q, (q : ℝ) * ∑ i ∈ I, (E q i) ^ 2 := by sorry
