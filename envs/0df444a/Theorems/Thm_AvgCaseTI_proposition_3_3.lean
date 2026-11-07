-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_3_3
-- name    : AvgCaseTI.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:47.526224+00:00
-- url     : https://prove2.me/theorems/85f811bc-1244-4f06-86e0-181c56d6ff75
-- title:
--   Proposition 3.3 — a random $n$-dimensional matrix code has a one-dimensional hull with probability $\pi_1(q)+o(1)=\Theta(1/q)$
-- statement:
--   Let $\mathcal A$ be a uniformly random $n$-dimensional subspace of $\mathrm M(n,q)$ and
--   $$
--   \pi_1(q)=\frac{1}{q-1}\prod_{j=1}^{\infty}\bigl(1-q^{-(2j-1)}\bigr).
--   $$
--   Then
--   1. for every finite field $\mathbb F_q$, $\Pr[\dim H(\mathcal A)=1]=\pi_1(q)+o(1)$ as $n\to\infty$;
--   2. $\pi_1(q)=\Theta(1/q)$: there are absolute constants $c_1,c_2>0$ with $c_1/q\le\pi_1(q)\le c_2/q$ for every finite field;
--   3. with the same constants, for every finite field, $c_1/q\le\Pr[\dim H(\mathcal A)=1]\le c_2/q$ for all sufficiently large $n$.
--
--   This is the step of the algorithm of Theorem 1.1 that costs the factor $1/\Theta(q)$ in its success fraction.
--
--   **Formalization Note** The constants $c_1,c_2$ are chosen before the field; the threshold on $n$ in clause 3 depends on the field.
--
--   Differences from the source:
--
--   - encoding: Pr[dim H(A) = 1] = π₁(q) + o(1) as n → ∞ → `Tendsto` of the probability to π₁(q), for each finite field; reason: same statement
--   - reading: "π₁(q) = Θ(1/q), and the probability is Θ(1/q)" → absolute constants c₁, c₂ > 0, chosen before the field, bounding both; reason: Θ with absolute constants is the paper's usage (p.17: 1/(4q) < π₁(q) ≤ 2/q)
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvgCaseTI_pi1
import Definitions.Def_AvgCaseTI_hullProb

set_option autoImplicit false

universe u

namespace AvgCaseTI

open Filter Topology

/-- **Proposition 3.3 (a random `n`-dimensional matrix code has a one-dimensional hull with
probability `Θ(1/q)`).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16
(PDF p.18). For a uniformly random `n`-dimensional subspace `𝒜 ≤ M(n, q)`:
1. for every finite field, `Pr[dim H(𝒜) = 1] = π₁(q) + o(1)` as `n → ∞`;
2. `π₁(q) = Θ(1/q)`: there are absolute constants `c₁, c₂ > 0` with `c₁/q ≤ π₁(q) ≤ c₂/q` for every
   finite field;
3. with the same constants, for every finite field, `c₁/q ≤ Pr[dim H(𝒜) = 1] ≤ c₂/q` for all
   sufficiently large `n`.

**Formalization Note.** `o(1)` is convergence for fixed `q`; `Θ` has absolute constants chosen before
the field; the threshold in 3 depends on the field. -/
theorem proposition_3_3 :
    (∀ (K : Type u) [Field K] [Fintype K],
      Tendsto (hullProb K) atTop (𝓝 (pi1 (Fintype.card K)))) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ (K : Type u) [Field K] [Fintype K],
        c₁ / (Fintype.card K : ℝ) ≤ pi1 (Fintype.card K) ∧
          pi1 (Fintype.card K) ≤ c₂ / (Fintype.card K : ℝ)) ∧
      ∀ (K : Type u) [Field K] [Fintype K], ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c₁ / (Fintype.card K : ℝ) ≤ hullProb K n ∧ hullProb K n ≤ c₂ / (Fintype.card K : ℝ) := by sorry

end AvgCaseTI
