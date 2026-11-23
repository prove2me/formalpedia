-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_flowCutAnswer_optimal
-- name    : ChenCapacityTerminals.Exact.flowCutAnswer_optimal
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:04:42.368482+00:00
-- url     : https://prove2.me/theorems/98c308ca-d22b-47f9-a33c-94790dd54133
-- title:
--   A valid flow-and-shore answer contains a minimum pair shore
-- statement:
--   In a valid directed arc-record network, if a nonnegative arc flow satisfies all capacity bounds, is conserved away from $r$ and $z$, and has divergence at $r$ equal to $f_D(X)$ for an $r$–$z$ sink side $X$, then $X$ is a minimum $r$–$z$ sink side. Loops, parallel arcs, antiparallel arcs, and zero-capacity arcs may occur.
--
--   For any other pair side $Y$, conservation together with nonnegativity gives
--   $$\operatorname{div}(r)\le f_D(Y).$$
--   By the assumed flow/cut equality, $\operatorname{div}(r)=f_D(X)$, proving minimality. This is the pure flow-accounting certificate used by the exact oracle: no path decomposition or integral-flow assumption is required.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Lemma 3.1 proof, p. 6, PDF p. 7 (the flow returned by the fixed-pair call gives a minimum augmented shore); standard conservation and weak-duality accounting for directed entering cuts.

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.flowCutAnswer_optimal (G : Network) (r z : ℕ) (flow : ℕ → ℝ) (X : Finset ℕ)
    (h : FlowCutAnswer G r z flow X) : OptimalPair G r z X := by sorry
