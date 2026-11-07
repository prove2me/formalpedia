-- Prove2me | Theorems.Thm_DynSort_theorem_1
-- name    : DynSort.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:47.97512+00:00
-- url     : https://prove2.me/theorems/42a7dc9b-8472-4a0f-9575-ef816e3d97ad
-- title:
--   Theorem 1 — fully dynamic sorting with competitive ratio $O(\log^2 n)$ and $O(\log^4 n)$ amortized recourse
-- statement:
--   There is a constant $C$ such that for every $n$ there is a deterministic online algorithm for the fully dynamic sorting problem on an array of exactly $n$ cells with the following property. For every valid sequence $\sigma$ of updates (insertions of arbitrary reals, duplicates allowed, and deletions, with at most $n$ elements present at any time):
--
--   1. the arrangement after $\sigma$ is legal: it stores exactly the elements present, each in one cell;
--   2. its stored sequence $S$ satisfies
--   $$\mathrm{cost}(S)\le C\log^2 n\cdot\mathrm{OPT}(S);$$
--   3. the total recourse over $\sigma$ satisfies
--   $$\sum_{t=1}^{|\sigma|}\mathrm{recourse}_t\le C\log^4 n\cdot|\sigma| .$$
--
--   Since every prefix of a valid sequence is valid, clauses 1 and 2 hold after every update and clause 3 for every prefix. This is the paper's main result: it shows that polylogarithmic recourse suffices for a polylogarithmic competitive ratio in the fully dynamic setting, where an algorithm that never moves elements has ratio $\Omega(n)$.
--
--   **Formalization Note** $\log$ is the natural logarithm; changing the base changes only $C$. For $n\le1$, $\log n=0$, and every legal algorithm has cost $0$ and recourse $0$ there.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm → a function from the update history to the arrangement of the n cells; reason: being a function of the history makes it online; the paper claims no running time, so no computation model is imposed
--   - encoding: the recourse of an update: previously stored elements that change positions → elements stored before and after the update at different cells; reason: a function of the history has no intermediate states, so the position change is net
--   - reading: competitive ratio O(log² n) → cost ≤ C·log²n·OPT after every update, with no additive term, one C for all n; reason: the stronger of the two usual readings; §5.4 proves it in this form
--   - encoding: O(log⁴ n) amortized recourse per update → total recourse over every valid σ ≤ C·log⁴n·|σ|, no additive term; reason: amortized recourse is the total divided by the number of updates (p.6)
--   - encoding: real-valued elements, arbitrary insertions and deletions → insert x for any real x and delete i of an alive element; elements named by the index of their insertion; reason: equal values are distinct elements, as in the paper
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_DynSort_OnlineAlg

namespace DynSort

/-- **Theorem 1**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §1.1, p.1 (PDF p.3): "There is a deterministic algorithm for the fully
dynamic sorting problem that maintains an array of size n under arbitrary insertions and
deletions, with competitive ratio O(log² n) and O(log⁴ n) amortized recourse per update."

**Formalization Note.** One constant `C`, chosen before `n`; for every `n` an online algorithm on
exactly `n` cells such that, for every valid update sequence `σ` (arbitrary reals, duplicates,
deletions, at most `n` elements present): the arrangement after `σ` is legal, its cost is at most
`C·log²n` times the optimum of the elements present, and the total recourse over `σ` is at most
`C·log⁴n·|σ|`. Prefixes of valid sequences are valid, so the first two clauses hold after every
update. `log` is `Real.log`, which is `0` at `n ≤ 1`, where every legal algorithm has cost and
recourse `0`. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ n : ℕ, ∃ alg : OnlineAlg n, ∀ σ : List Update, Valid n σ →
      Legal n σ (alg σ) ∧
      cost (seq σ (alg σ)) ≤ C * Real.log n ^ 2 * opt (seq σ (alg σ)) ∧
      (totalRecourse alg σ : ℝ) ≤ C * Real.log n ^ 4 * σ.length := by sorry

end DynSort
