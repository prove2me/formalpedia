-- Prove2me | Theorems.Thm_AndOrSched_lemma_2
-- name    : AndOrSched.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:07.161566+00:00
-- url     : https://prove2.me/theorems/71aca048-9392-4155-ae35-639d72eef7bb
-- title:
--   Lemma 2, p.8 — $O(n^2)$ different $\beta$-schedules
-- statement:
--   Let the instance have integer processing times $p_j\in\{0,1\}$ and let $x$ be a feasible solution of LP (1). Then the candidate set $\mathcal B(x)$ of values of $\beta$ satisfies
--   1. $\mathcal B(x)\subseteq(0,1]$;
--   2. $T\le n$ and $|\mathcal B(x)|\le n\cdot T+1$, so $|\mathcal B(x)|=O(n^2)$;
--   3. for every $\beta\in(0,1]$ some $\hat\beta\in\mathcal B(x)$ gives every job the same sort key as $\beta$, hence the same compatible orders and the same $\beta$-schedules.
--
--   Differences from the source:
--   - encoding: O(n²) different β-schedules → an explicit candidate set of size ≤ n·T + 1 with T ≤ n, reaching every key vector of β ∈ (0, 1]; reason: the β-schedules depend on β only through the keys; the constant is made explicit
--   - generalization: x̄ (an optimal solution) → x any feasible solution of LP (1); reason: the count uses only (1b) and (1f)
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, Lemma 2, p.8, "For every x̄ there are O(n2) different β-schedules."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
open scoped Classical NNReal

namespace AndOrSched

/-- Lemma 2, p.8 (Happach, Schulz, arXiv:2001.07011v1): "For every x̄ there are O(n2) different β-schedules."

For an instance with integer processing times at most `1` and every feasible solution `x` of LP (1):
the candidate set lies in `(0, 1]` and has at most `n · T + 1` elements, `T ≤ n`, and every
`β ∈ (0, 1]` has a candidate with the same sort keys, hence the same `β`-schedules. -/
theorem lemma_2 (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) :
    (∀ β ∈ cand I x (horizon I), 0 < β ∧ β ≤ 1) ∧
    horizon I ≤ Fintype.card I.N ∧
    (cand I x (horizon I)).card ≤ Fintype.card I.N * horizon I + 1 ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ β' ∈ cand I x (horizon I), key I x β' = key I x β := by sorry

end AndOrSched
