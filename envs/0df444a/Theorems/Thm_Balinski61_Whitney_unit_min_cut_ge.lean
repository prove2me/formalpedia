-- Prove2me | Theorems.Thm_Balinski61_Whitney_unit_min_cut_ge
-- name    : Balinski61.Whitney.unit_min_cut_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:43.78799+00:00
-- url     : https://prove2.me/theorems/17d848df-1e19-4ef2-b9dc-203d5f54a4e8
-- title:
--   p. 434, proof of WHITNEY'S THEOREM — in the unit network every disconnecting set has value at least n
-- statement:
--   Let $G$ be an $n$-tuply connected finite graph and $p_s \ne p_k$ two of its points. Give $G$ the capacities of Whitney's proof: $1$ on every point except $p_s, p_k$ (which get $n+1$), $n+1$ on every line except the line $p_sp_k$ (if present), which gets $1$. Then every disconnecting set $(X,F)$ for $p_s$ and $p_k$ has value at least $n$:
--   $$
--   \sum_{x\in X} c(x) + \sum_{e\in F} c(e) \;\ge\; n .
--   $$
--
--   In the paper this is the step "the min-cut $< n$ contradicts the $n$-tuple connectedness of $G$", which gives max-flow $\ge n$ through the max-flow min-cut theorem.
--
--   **Formalization Note** The paper's argument does not discuss a disconnecting set that contains the line $p_sp_k$ (capacity $1$) together with at most $n-2$ points; the statement covers that case too and remains true. Source and sink have capacity $n+1$, a choice the paper leaves open. No connectivity hypothesis beyond $n$-tuple connectedness is assumed, so the statement is also meaningful (and trivial) at $n = 0$.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, proof of WHITNEY'S THEOREM

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph
import Definitions.Def_Balinski61_Whitney_Network
import Definitions.Def_Balinski61_Whitney_UnitNetwork

namespace Balinski61.Whitney

theorem unit_min_cut_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (ps pk : V)
    (hG : IsNTuplyConnected G n) (hst : ps ≠ pk) :
    ∀ (X : Finset V) (F : Finset (Sym2 V)), IsDisconnecting G ps pk X F →
      (n : ℝ) ≤ cutValue (unitCapV ps pk n) (unitCapE ps pk n) X F := by sorry

end Balinski61.Whitney
