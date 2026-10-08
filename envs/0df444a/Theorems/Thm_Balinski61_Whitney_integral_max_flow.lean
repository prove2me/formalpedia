-- Prove2me | Theorems.Thm_Balinski61_Whitney_integral_max_flow
-- name    : Balinski61.Whitney.integral_max_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:05:29.533308+00:00
-- url     : https://prove2.me/theorems/b23f661e-b2e5-4365-b129-b214962d5b72
-- title:
--   pp. 433–434 — with integer capacities there is a maximum flow with integer path flows
-- statement:
--   Let $G$ be a connected finite graph with nonnegative capacities $c(x)$ on its points and $c(e)$ on its lines, all of them integers, and let $p_s \ne p_k$ be the source and the sink. Then there is a maximum flow all of whose path flows are integers: a flow $f$ with
--   $$
--   \operatorname{val}(g) \le \operatorname{val}(f) \ \text{ for every flow } g, \qquad f(C) \in \mathbb Z \ \text{ for every path } C.
--   $$
--
--   The paper states this remark without proof right after the max-flow min-cut theorem; it is what turns the flow value into a count of paths in Whitney's proof.
--
--   **Formalization Note** Integrality of a capacity is written $\exists z \in \mathbb Z,\ c = z$; for lines it is required only on lines of $G$. Flows are path flows on simple paths, as in the definition file.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), pp. 433–434, remark after THE MAX-FLOW MIN-CUT THEOREM

import Mathlib
import Definitions.Def_Balinski61_Whitney_Network

namespace Balinski61.Whitney

theorem integral_max_flow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (capV : V → ℝ) (capE : Sym2 V → ℝ) (ps pk : V)
    (hG : G.Connected) (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e)
    (hst : ps ≠ pk)
    (hintV : ∀ x, ∃ z : ℤ, capV x = z) (hintE : ∀ e ∈ G.edgeSet, ∃ z : ℤ, capE e = z) :
    ∃ f : G.Path ps pk → ℝ, IsFlow G capV capE ps pk f ∧
      (∀ g : G.Path ps pk → ℝ, IsFlow G capV capE ps pk g → flowValue G g ≤ flowValue G f) ∧
      ∀ C, ∃ z : ℤ, f C = z := by sorry

end Balinski61.Whitney
