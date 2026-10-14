-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_feasible_flows_complete_lattice
-- name    : FlowAllocGames.StrongEq.feasible_flows_complete_lattice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:31.331318+00:00
-- url     : https://prove2.me/theorems/0f43f350-aef5-4cd6-a614-8db14a69f22e
-- title:
--   Theorem 2, p. 12 (integral version p. 13) — the feasible flows of a monotone profile form a non-empty complete lattice
-- statement:
--   Let $\Gamma$ be a flow allocation game and $\mathbf a = (a_e)_{e\in E}$ a profile of integral strategies $a_e : \mathbb{N}_0 \to \mathbb{N}_0$ that are *monotone*: for all $y, y'$, every edge $e$ and every node $v$,
--
--   1. $0 \le a_e(y) \le c_e$ (capacity),
--   2. $\sum_{e\in E^+(v)} a_e(y) \le y$ (weak flow conservation),
--   3. $y \ge y'$ implies $a_e(y) \ge a_e(y')$ (monotonicity).
--
--   Let $\mathcal F$ be the set of integral flows feasible for $\mathbf a$, ordered coordinatewise. Then $(\mathcal F, \le)$ is a non-empty complete lattice: every subset $S \subseteq \mathcal F$ has a least upper bound inside $\mathcal F$. Moreover the clearing state $\hat{\mathbf f}$, defined coordinatewise by
--
--   $$\hat f_e = \sup\{f_e : \mathbf f \in \mathcal F\},$$
--
--   is itself a feasible flow and the greatest element of $\mathcal F$.
--
--   The result is due to Csóka and Herings and follows from the Knaster–Tarski fixed-point theorem applied to the order-preserving map $g(\mathbf f)_{(u,v)} = a_{(u,v)}(\sum_{e'\in E^-(u)} f_{e'} + b_u)$ on the finite lattice of flows bounded by the capacities. It is what makes the clearing state, and hence utilities and $\mathrm{Flow}$, well defined.
--
--   **Formalization Note.** "Complete lattice" is stated as: every subset of $\mathcal F$, including $\emptyset$ (which gives non-emptiness), has a least upper bound in $(\mathcal F, \le)$. The no-fraud constraint (3) of unit-ranking profiles is not assumed, as on the page. The second conjunct ties the definition of the clearing state as a coordinatewise supremum in $\mathbb N$ to the feasible flows.
-- source:
--   arXiv:1908.01714v3, Theorem 2, p. 12; integral version, §2.2 Unit-ranking strategies, p. 13

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

/-- Theorem 2 (arXiv:1908.01714v3, p. 12), in its integral version (p. 13): for a profile of
integral monotone strategies (capacity (1), weak flow conservation (2), monotonicity (5)), the
feasible flows form a non-empty complete lattice under the coordinatewise order, and the clearing
state is its greatest element. -/
theorem feasible_flows_complete_lattice {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) (a : Profile E) (h1 : ∀ e y, a e y ≤ G.c e)
    (h2 : ∀ v y, ∑ e ∈ G.outEdges v, a e y ≤ y) (h5 : ∀ e, Monotone (a e)) :
    (∀ S ⊆ {f | G.IsFeasible a f}, ∃ f ∈ {f | G.IsFeasible a f}, f ∈ upperBounds S ∧
      ∀ g ∈ {f | G.IsFeasible a f}, g ∈ upperBounds S → f ≤ g) ∧
    IsGreatest {f | G.IsFeasible a f} (G.clearingState a) := by sorry

end FlowAllocGames.StrongEq
