-- Prove2me | Theorems.Thm_CanadaCTP_lemma_9
-- name    : CanadaCTP.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:50.068551+00:00
-- url     : https://prove2.me/theorems/7cd4e111-6dcc-4848-a434-089180b21d41
-- title:
--   Lemma 9 — SumMaximizer solves MaxSum optimally in time $O(\sum_i d_i\max(d_i,\log k))$
-- statement:
--   There is a constant $C$ such that for every $k\ge1$, all paths $X^1,\dots,X^k$ and every budget $b\ge0$, the budgets $(b_i)$ returned by SumMaximizer solve MaxSum (Definition 3): $b_i\ge0$, $\sum_ib_i=b$, and
--   $$
--   \sum_{i=1}^k\mathrm{prob}_{X^i}(b_i)\ \ge\ \sum_{i=1}^k\mathrm{prob}_{X^i}(b'_i)\quad\text{for all } b'\in\mathbb R^k_{\ge0}\text{ with }\textstyle\sum_ib'_i=b .
--   $$
--   If every path has at least one edge, the number of counted operations is at most
--   $$
--   C\Big(1+\sum_{i=1}^k d_i\max(d_i,\log k)\Big),\qquad d_i=\sum_{j=1}^{m_i}|\operatorname{supp}X^i_j| .
--   $$
--
--   It is the budget split of every phase of ParallelTraveller.
--
--   **Formalization Note** The paper writes $\mathbb N_0$ for $\mathbb N\cup\{0\}$, so "$k\in\mathbb N$" is $k\ge1$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: k ∈ ℕ sequences → 0 < k; reason: the paper writes ℕ₀ for ℕ ∪ {0}, so ℕ starts at 1
--   - reading: time O(Σ d_i·max(d_i, log k)) for sequences X^i = (X^i_1, …, X^i_{m_i}) → the time bound under m_i ≥ 1 for every i; optimality for every m_i ≥ 0; reason: the notation X^i_1, …, X^i_{m_i} and the use in Algorithm 1 (paths of a disjoint-path graph) have m_i ≥ 1; with m_i = 0 for all i the printed bound is O(0) although the k lists must still be read
--   - encoding: O(·) → ∃ C, ops ≤ C·(1 + ·), one C for all inputs; Work operation counter; reason: unit-cost operation count of the named program; the +1 only matters where the expression is 0
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 9, p.15; proof pp.39–40; Definition 3, p.6

import Mathlib
import Definitions.Def_CanadaCTP_SumMaximizer

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 9, p.15 (proof pp.39–40), with Definition 3 (p.6): SumMaximizer solves MaxSum
optimally — its budgets are non-negative, sum to `b`, and maximize `Σᵢ prob_{Xⁱ}(bᵢ)` over all
such budget vectors — in time `O(Σᵢ dᵢ·max(dᵢ, log k))`, one constant for all inputs.

**Formalization Note.** `k ∈ ℕ` means `k ≥ 1` in the paper (it writes `ℕ₀` for `ℕ ∪ {0}`). The
time bound is stated for sequences `Xⁱ = (Xⁱ₁, …, Xⁱ_{mᵢ})` with `mᵢ ≥ 1`, the MaxSum instances of
Algorithm 1; with `mᵢ = 0` for many `i` the printed bound would be `O(0)` although the `k` lists
must still be handled. `O(·)` is `≤ C·(1 + ·)`; `log` is the natural logarithm. -/
theorem lemma_9 : ∃ C : ℝ, ∀ (k : ℕ) (Xs : Fin k → Σ m : ℕ, (Fin m → EdgeDist)) (b : ℝ),
    0 < k → 0 ≤ b →
    (∀ i, 0 ≤ ((sumMaximizer Xs b).run 0).1 i) ∧
    ∑ i, ((sumMaximizer Xs b).run 0).1 i = b ∧
    (∀ b' : Fin k → ℝ, (∀ i, 0 ≤ b' i) → ∑ i, b' i = b →
      ∑ i, probX (Xs i).2 (b' i) ≤ ∑ i, probX (Xs i).2 (((sumMaximizer Xs b).run 0).1 i)) ∧
    ((∀ i, 0 < (Xs i).1) →
      ((((sumMaximizer Xs b).run 0).2 : ℕ) : ℝ) ≤
        C * (1 + ∑ i, (dX (Xs i).2 : ℝ) * max (dX (Xs i).2 : ℝ) (Real.log k))) := by sorry

end CanadaCTP
