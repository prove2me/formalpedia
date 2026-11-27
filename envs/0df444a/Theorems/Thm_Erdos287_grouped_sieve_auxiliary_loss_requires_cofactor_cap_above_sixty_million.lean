-- Prove2me | Theorems.Thm_Erdos287_grouped_sieve_auxiliary_loss_requires_cofactor_cap_above_sixty_million
-- name    : Erdos287.grouped_sieve_auxiliary_loss_requires_cofactor_cap_above_sixty_million
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:13:29.181375+00:00
-- url     : https://prove2.me/theorems/7fa4ddf1-0651-5b71-befe-c4ac8325bdbc
-- title:
--   The auxiliary level loss requires a cofactor budget above sixty million
-- statement:
--   For the one-period grouped moment argument with $v/u<e$, assume simplex radius $\sigma\le1/4$, cofactor budget $B\le60{,}000{,}000$, form count $T\le2BN$, average mean $N\mu\le2\sigma\log(1+T)$, and pair coefficient $2/(1-2\sigma)\le A<r=N/u$. Then the necessary strict moment inequality fails.
-- source:
--   Erdős Problem 287. Quantitative limits on a finite splice for the grouped sieve.

import Mathlib

theorem Erdos287.grouped_sieve_auxiliary_loss_requires_cofactor_cap_above_sixty_million (B u v : ℕ) (T σ A μ : ℝ) (hB : B ≤ 60000000) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ)) (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N →
    2 / (1 - 2 * σ) ≤ A → A < r →
    N * μ ≤ 2 * σ * Real.log (1 + T) →
    μ * (r - A) ≤ 1 - A * σ := by sorry
