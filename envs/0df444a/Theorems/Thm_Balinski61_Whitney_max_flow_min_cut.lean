-- Prove2me | Theorems.Thm_Balinski61_Whitney_max_flow_min_cut
-- name    : Balinski61.Whitney.max_flow_min_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:02.154997+00:00
-- url     : https://prove2.me/theorems/495c69de-e723-4d8d-89a8-6b3f2dfbf75e
-- title:
--   p. 433, THE MAX-FLOW MIN-CUT THEOREM with capacities on points and lines
-- statement:
--   Let $G$ be a connected finite graph with nonnegative capacities $c(x)$ on its points and $c(e)$ on its lines, and let $p_s \ne p_k$ be the source and the sink. Then the maximum of the values of all flows from $p_s$ to $p_k$ equals the minimum of the values of all disconnecting sets: there is a number $M$ such that
--
--   1. some flow has value $M$, and every flow has value at most $M$;
--   2. some disconnecting set has value $M$, and every disconnecting set has value at least $M$.
--
--   $$
--   \max_{f \text{ flow}} \operatorname{val}(f) \;=\; M \;=\; \min_{(X,F) \text{ disconnecting}} \Bigl(\sum_{x\in X} c(x) + \sum_{e\in F} c(e)\Bigr).
--   $$
--
--   The paper cites this theorem from Dantzig–Fulkerson and Ford–Fulkerson ([3], [5]) and uses it as the engine of its proof of Whitney's theorem.
--
--   **Formalization Note** Both the maximum and the minimum are stated as attained, not as a supremum and infimum. Flows are path flows on simple paths (see the definition file); capacities and cuts include points and lines, and the source and sink carry capacities like every other point. "Network" in the paper includes connectivity of $G$, kept here as a hypothesis.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 433, THE MAX-FLOW MIN-CUT THEOREM [3], [5]

import Mathlib
import Definitions.Def_Balinski61_Whitney_Network

namespace Balinski61.Whitney

theorem max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (capV : V → ℝ) (capE : Sym2 V → ℝ) (ps pk : V)
    (hG : G.Connected) (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e)
    (hst : ps ≠ pk) :
    ∃ M : ℝ,
      (∃ f : G.Path ps pk → ℝ, IsFlow G capV capE ps pk f ∧ flowValue G f = M) ∧
      (∀ f : G.Path ps pk → ℝ, IsFlow G capV capE ps pk f → flowValue G f ≤ M) ∧
      (∃ (X : Finset V) (F : Finset (Sym2 V)),
        IsDisconnecting G ps pk X F ∧ cutValue capV capE X F = M) ∧
      (∀ (X : Finset V) (F : Finset (Sym2 V)),
        IsDisconnecting G ps pk X F → M ≤ cutValue capV capE X F) := by sorry

end Balinski61.Whitney
