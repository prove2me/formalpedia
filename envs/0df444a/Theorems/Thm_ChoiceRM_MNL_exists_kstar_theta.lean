-- Prove2me | Theorems.Thm_ChoiceRM_MNL_exists_kstar_theta
-- name    : ChoiceRM.MNL.exists_kstar_theta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:21.691401+00:00
-- url     : https://prove2.me/theorems/79e4ed14-4b68-4452-ae06-2af518d1d7ae
-- title:
--   Proof of Proposition 6, p. 24, (15) — the index k* and the weight λ for an incomplete set
-- statement:
--   Let $w_1, \dots, w_n > 0$, write $W(S) = \sum_{i \in S} w_i$, and let $T \subseteq N$ be incomplete (not of the form $A_k = \{1, \dots, k\}$, $0 \le k \le n$). Then there is an index $k^*$ with $0 \le k^* < n$ such that
--
--   1. $W(A_{k^*}) \le W(T) < W(A_{k^*+1})$;
--   2. $T$ contains a product with index larger than $k^*$, i.e. $\max\{j : j \in T\} > k^*$;
--   3. there is $\theta \in [0, 1]$ with
--   $$
--   \theta \frac{W(A_{k^*})}{W(A_{k^*}) + 1} + (1 - \theta) \frac{W(A_{k^*+1})}{W(A_{k^*+1}) + 1} = \frac{W(T)}{W(T) + 1}. \qquad (15)
--   $$
--
--   The two complete sets $A_{k^*}$ and $A_{k^*+1}$, mixed with weights $\theta$ and $1-\theta$, are the convex combination that the proof of Proposition 6 compares with $T$.
--
--   **Formalization Note** The paper's $\lambda$ is written $\theta$ (`λ` is reserved in Lean). Products are `Fin n`, so "$\max\{j : j\in T\} > k^*$" in the paper's 1-based indexing is "some $j \in T$ with `k ≤ j.val`" in 0-based indexing, and $A_k$ is `complete n k`. The page says "define $\lambda$ by (15)"; that a solution exists and lies in $[0,1]$, so that the weights are convex, is implicit there and is what this item asserts.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 24, proof of Proposition 6, definition of k* and eq. (15)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder
import Definitions.Def_ChoiceRM_MNL_Models

namespace ChoiceRM.MNL

/-- Proof of Proposition 6, p. 24, (15): for an incomplete set `T` there is an index `k*` with
`W(A_{k*}) ≤ W(T) < W(A_{k*+1})` (where `W(S) = Σ_{i∈S} w_i`), `T` contains a fare beyond
`A_{k*}`, and a weight `θ ∈ [0, 1]` (the paper's `λ`) solving (15). -/
theorem exists_kstar_theta {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (T : Finset (Fin n)) (hT : ¬ IsComplete T) :
    ∃ k < n,
      ∑ i ∈ complete n k, w i ≤ ∑ i ∈ T, w i ∧
      ∑ i ∈ T, w i < ∑ i ∈ complete n (k + 1), w i ∧
      (∃ j ∈ T, k ≤ j.val) ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
        θ * ((∑ i ∈ complete n k, w i) / (∑ i ∈ complete n k, w i + 1)) +
            (1 - θ) * ((∑ i ∈ complete n (k + 1), w i) /
              (∑ i ∈ complete n (k + 1), w i + 1)) =
          (∑ i ∈ T, w i) / (∑ i ∈ T, w i + 1) := by sorry

end ChoiceRM.MNL
