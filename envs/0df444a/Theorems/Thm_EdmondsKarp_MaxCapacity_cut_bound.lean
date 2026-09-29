-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_cut_bound
-- name    : EdmondsKarp.MaxCapacity.cut_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:20:02.340028+00:00
-- url     : https://prove2.me/theorems/3c2918d5-4244-440f-8abc-636b601b73b1
-- title:
--   Cut inequality: $c(X,\bar X) \ge f(X,\bar X) - f(\bar X,X) = f(t,s)$
-- statement:
--   Let $N$ be a network with integer capacities, and let $X$ be a set of nodes with $s \in X$ and $t \notin X$; write $\bar X$ for its complement. For every flow $f$ in $N$,
--   $$c(X,\bar X) \;\ge\; f(X,\bar X) - f(\bar X,X) \;=\; f(t,s),$$
--   where $c(X,\bar X)$ and $f(X,\bar X)$ sum over the arcs of $A$ from $X$ to $\bar X$ and $f(\bar X,X)$ over the arcs of $A$ from $\bar X$ to $X$ (the return arc is not in $A$).
--
--   The net flow across any $s$–$t$ cut equals the value on the return arc and is bounded by the cut's capacity; applied to a maximum flow it gives $f^*(t,s) \le c(X,\bar X)$, the first step of the proof of Theorem 2.
--
--   **Formalization Note** The integrality of the capacities is the standing assumption of §1.3 and is kept as a hypothesis, although the inequality does not need it.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 254, proof of Theorem 2 (displayed definitions of c(X, X̄), f(X, X̄), f(X̄, X) and "Then, for any flow f, c(X, X̄) ≥ f(X, X̄) − f(X̄, X) = f(t, s).")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

/-- Proof of Theorem 2, p. 254: for a network `N` with integer capacities, a set of nodes `X` with
`s ∈ X`, `t ∉ X`, and any flow `f`: `c(X, X̄) ≥ f(X, X̄) − f(X̄, X) = f(t, s)`. -/
theorem cut_bound {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    cutFlowOut N f X - cutFlowIn N f X = f N.t N.s ∧
      cutFlowOut N f X - cutFlowIn N f X ≤ cutCap N X := by sorry

end EdmondsKarp.MaxCapacity
