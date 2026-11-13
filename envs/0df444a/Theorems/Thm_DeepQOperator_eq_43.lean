-- Prove2me | Theorems.Thm_DeepQOperator_eq_43
-- name    : DeepQOperator.eq_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:08.428031+00:00
-- url     : https://prove2.me/theorems/2eccb9b2-157c-4f44-8f7f-6a8a59d31b55
-- title:
--   (43): the squared Walsh scores sum to at most $1/4$ on the address cube
-- statement:
--   For the family (6) with $m\ge2$ and $b_i(a)=c_i^{\mathsf T}a/(2n)$,
--   $$\sum_{i=0}^{m-1}b_i(a)^2\le\frac{\|a\|_2^2}{4n}\qquad\text{for every }a\in\mathbb R^n,$$
--   and on the entire address cube $a\in[-1,1]^n$ the sum is at most $1/4$.
--
--   Because at most $64$ scores can then exceed $1/16$, this bound limits the candidate set of Theorem 2's protocol.
--
--   **Formalization Note** The address is the address part of $\theta=(a,z)$.
--
--   Differences from the source:
--   - generalization: the chain Σ b_i² ≤ ∥a∥²/(4n) ≤ 1/4 on the address cube → the first inequality for every address in ℝ^n, the second on the cube; reason: the first link uses no bound on a; on the cube both hold as printed
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, eq. (43), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator

/-- **(43)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, p.23, PDF p.26; = (35) of Appendix D.1).

For the family (6) with `m ≥ 2` and `b_i = c_iᵀa/(2n)`: `Σ_i b_i² ≤ ∥a∥₂²/(4n)`, and on the entire
address cube `[-1,1]^n` this is at most `1/4`.

**Formalization Note.** The address of `θ : Coord m → ℝ` is `v ↦ θ (Sum.inl v)`. The first inequality
is stated for every address in `ℝ^n` (the paper states the chain on the cube; the first link uses no
bound on `a`), the second assumes only the address cube.
-/
theorem eq_43 (m : ℕ) (hm : 2 ≤ m) (θ : Coord m → ℝ) :
    ∑ i : Fin m, bScore m i θ ^ 2 ≤ (∑ v : Addr m, θ (Sum.inl v) ^ 2) / (4 * (nn m : ℝ)) ∧
    ((∀ v : Addr m, θ (Sum.inl v) ∈ Set.Icc (-1 : ℝ) 1) → ∑ i : Fin m, bScore m i θ ^ 2 ≤ 1 / 4) := by sorry

end DeepQOperator
