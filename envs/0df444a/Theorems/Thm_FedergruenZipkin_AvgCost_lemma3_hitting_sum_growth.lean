-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma3_hitting_sum_growth
-- name    : FedergruenZipkin.AvgCost.lemma3_hitting_sum_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:37:44.594981+00:00
-- url     : https://prove2.me/theorems/6d853cfa-59af-425d-bd0c-91cb2026cfc3
-- title:
--   Lemma 3 (p. 198) — if $v = O(|x|^q)$ then $H_\iota v = O(|x|^{q+3})$
-- statement:
--   Consider the capacitated inventory model with storage capacity $U$. Let $\iota$ be the integers in a finite interval $[l, u]$ with $0 \le u \le U$ and $l \le u - b$. Let $\Delta_\iota$ be the set of feasible policies $\delta$ with $\delta(x) = x + b$ for $x \le l$ and $\delta(x) = x$ for $u \le x \le U$, let $T(\iota)$ be the first period $t \ge 1$ with $x_t \in \iota$ (so $T(\iota) > 0$ even if $x_0 \in \iota$), and for a function $v$ on the integers let
--   $$H_\iota v(x) = \max_{\delta\in\Delta_\iota} E\Bigl\{\sum_{t=0}^{T(\iota)-1} v(y_t) \Bigm| x_0 = x, \delta\Bigr\},\qquad x \le U.$$
--
--   **Lemma 3.** If $v(x) = O(|x|^q)$ for a positive integer $q$, then $H_\iota v(x) = O(|x|^{q+3})$. Precisely: if $|v(x)| \le A + B|x|^q$ for all $x \le U$, then there are constants $A', B'$ with
--   $$H_\iota |v|(x) \le A' + B'|x|^{q+3}\qquad\text{for all } x \le U.$$
--
--   This is the paper's central technical estimate: it yields the finiteness and growth of the expected cost and the expected time until the inventory first returns to $\iota$, which is what the existence of a solution to the average-cost optimality equation rests on.
--
--   **Formalization Note** The bound is stated for $H_\iota$ applied to $|v|$, which dominates $|H_\iota v|$; the paper's proof bounds $|H_\iota v(x)|$ through $|v|$ as well. $H_\iota$ is $[0,\infty]$-valued and its maximum over $\Delta_\iota$ is a supremum, so the bound also asserts finiteness. The constants $A', B'$ may depend on $v$, $q$, $l$, $u$, $U$ and the model, but not on $x$. The model's standing assumptions (Assumptions 1–4, $c = 0$) are fields of `Model`.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, pp. 197-198, Lemma 3 (with the definitions of ι, Δ_ι, T(ι), H_ι preceding it)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem lemma3_hitting_sum_growth (M : Model) (U : ℤ) (q : ℕ) (hq : 0 < q) (v : ℤ → ℝ)
    (hv : ∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ q)
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b) :
    ∃ A' B' : ℝ, ∀ x ≤ U,
      H M U l u (fun z => ENNReal.ofReal |v z|) x ≤ ENNReal.ofReal (A' + B' * |(x : ℝ)| ^ (q + 3)) := by sorry
end FedergruenZipkin.AvgCost
