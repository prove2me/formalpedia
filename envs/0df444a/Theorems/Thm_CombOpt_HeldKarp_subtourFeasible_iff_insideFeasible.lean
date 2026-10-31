-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_subtourFeasible_iff_insideFeasible
-- name    : CombOpt.HeldKarp.subtourFeasible_iff_insideFeasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:30.33631+00:00
-- url     : https://prove2.me/theorems/e2cb7025-6ce6-401b-88ed-5e5f5c48d9df
-- title:
--   (7.1) = (7.2): the subtour LP in inside form has the same feasible set (corrected: no loop away from $v_1$, $S\ne\emptyset$ in (7.4))
-- statement:
--   Let $G=(V,E)$ be a finite graph (parallel edges allowed) and let $v_1\in V$ be a node such that every loop of $G$ is at $v_1$. For every $x\in\mathbb R^E$, the following are equivalent:
--
--   1. $x(\delta(v))=2$ for all $v\in V$; $x(\delta(S))\ge2$ for all $\emptyset\ne S\ne V$; $0\le x_e\le1$ for all $e$ (the constraints of (7.1));
--   2. $x(\delta(v))=2$ for all $v\in V$ (7.3); $x(\gamma(S))\le|S|-1$ for all nonempty $S\subseteq V$ with $v_1\notin S$ (7.4); $x(\gamma(V\setminus\{v_1\}))=|V|-2$ (7.5); $0\le x_e\le1$ for all $e$ (7.6).
--
--   Hence (7.1) and (7.2) are the same linear program. The inside form separates the edges at $v_1$ from the rest, which exposes the spanning-tree structure behind the Held–Karp bound.
--
--   Differences from the source:
--   - correction: any graph G → every loop of G is at v_1; reason: counterexample: triangle v_1ab plus a loop ℓ at a; x ≡ 1 (including x_ℓ = 1) satisfies (7.1), since a loop is in no cut, but violates (7.4) for S = {a}, where x(γ({a})) = x_ℓ = 1 > 0
--   - generalization: G is the complete graph of the TSP model (§7.1, p. 241) → any finite graph whose loops are all at v_1, parallel edges allowed; reason: §7.3 takes "a graph G" in its boxes and in the Held-Karp method; a complete graph is simple, hence an instance, so the statement specializes to the complete case
--   - correction: (7.4) for all S ⊆ V with v_1 ∉ S → (7.4) for all nonempty S ⊆ V with v_1 ∉ S; reason: at S = ∅ the printed constraint reads 0 ≤ −1, so (7.2) as printed is infeasible; counterexample: the triangle with x ≡ 1 is feasible for (7.1); the inside form of x(δ(S)) ≥ 2 (∅ ≠ S ≠ V) concerns nonempty S only
--   - reading: "we can write (7.1) as (7.2)" → the two constraint systems have the same feasible set; reason: the stronger of the two readings (same feasible set rather than same optimal value); it implies the other
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.1)–(7.6), p. 259 (PDF p. 267)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_SubtourFeasible
import Definitions.Def_CombOpt_HeldKarp_Graph_InsideFeasible

namespace CombOpt.HeldKarp

/-- **(7.1) can be written as (7.2): the subtour LP and its "inside" form have the same feasible
set (corrected: no loop away from v₁, S ≠ ∅ in (7.4)).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3,
p. 259 (PDF p. 267): "choose some node v_1 ∈ V and notice that we can restrict the set of subtour
constraints to those sets S that do not contain v_1 … making use of the equations x(δ(v)) = 2, we
can write the subtour constraints in the 'inside' form x(γ(S)) ≤ |S| − 1 … Also, the equation
x(γ(V \ {v_1})) = |V| − 2 is implied by the equations x(δ(v)) = 2 … With these modifications, we
can write (7.1) as [(7.2)–(7.6)]."

For a finite graph `G`, a node `v₁` such that every loop of `G` is at `v₁`, and `x : E → ℝ`: `x`
satisfies the constraints of (7.1) if and only if it satisfies (7.3)–(7.6) (with `S ≠ ∅` in (7.4)).

**Formalization Note.** Two corrections. (i) `S ≠ ∅` in (7.4): as printed, `S = ∅` gives `0 ≤ −1`.
(ii) No loop away from `v₁`: a loop at `u ≠ v₁` lies in `γ({u})`, so (7.4) forces its value to 0,
whereas (7.1) allows any value in `[0, 1]` (a loop is in no cut). A loop at `v₁` is in no `γ(S)` with
`v₁ ∉ S` and in no cut, so it is unconstrained on both sides and stays allowed. -/
theorem subtourFeasible_iff_insideFeasible {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Graph V E) (v₁ : V) (hG : ∀ (e : E) (u : V), G.ends e = s(u, u) → u = v₁) (x : E → ℝ) :
    G.SubtourFeasible x ↔ G.InsideFeasible v₁ x := by sorry

end CombOpt.HeldKarp
