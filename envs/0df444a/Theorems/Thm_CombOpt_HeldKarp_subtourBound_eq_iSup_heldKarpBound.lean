-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_subtourBound_eq_iSup_heldKarpBound
-- name    : CombOpt.HeldKarp.subtourBound_eq_iSup_heldKarpBound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:15:24.47498+00:00
-- url     : https://prove2.me/theorems/76e785b6-f853-474e-940b-2d65cae3e7e0
-- title:
--   Theorem 7.2: the subtour bound equals the optimal Held–Karp bound (corrected: loopless)
-- statement:
--   Let $G=(V,E)$ be a finite graph without loops (parallel edges allowed), $c\in\mathbb R^E$ edge costs, and $v_1\in V$ any node. Then
--   $$\min\{c^Tx : x \text{ feasible for (7.1)}\} \;=\; \sup_{y\in\mathbb R^V}\Big(2\sum_{v\in V}y_v + C_y\Big),$$
--   where (7.1) is the subtour linear program
--   $$x(\delta(v))=2\ (v\in V),\quad x(\delta(S))\ge2\ (\emptyset\ne S\ne V),\quad 0\le x_e\le 1\ (e\in E),$$
--   and $C_y$ is the 1-tree bound of $G$ (with respect to $v_1$) for the altered costs $\bar c_e=c_e-y_u-y_v$ ($e$ with ends $u,v$). Both sides are $+\infty$ when (7.1) is infeasible. When the left side is not $+\infty$ the supremum is a maximum: some $y$ attains it.
--
--   In words: **the subtour bound is equal to the optimal Held–Karp bound** (Held and Karp 1970). The Held–Karp subgradient procedure, which only ever computes minimum spanning trees, therefore approximates the optimal value of the Dantzig–Fulkerson–Johnson linear programming relaxation of the TSP.
--
--   Differences from the source:
--   - correction: any graph G → G has no loop; reason: counterexample: triangle v_1ab with costs 0 plus a loop at a of cost −1; the loop is in no cut, so (7.1) sets it to 1 and the subtour bound is −1, while every Held–Karp bound is 0
--   - generalization: G is the complete graph of the TSP model (§7.1, p. 241) → any finite loopless graph, parallel edges allowed; reason: §7.3 takes "a graph G" in its boxes and in the Held-Karp method; a complete graph is simple, hence an instance, so the statement specializes to the complete case
--   - reading: the maximum Held–Karp bound over all choices of node numbers → supremum over all y : V → ℝ, attained whenever the subtour bound is not +∞; reason: the stronger reading; when (7.1) is infeasible but G has 1-trees every Held–Karp bound is real and the supremum +∞ is not attained, so no maximum exists there and attainment cannot be claimed
--   - encoding: optimal values of (7.1) and of the bounds → EReal, +∞ for an infeasible (7.1) or an empty 1-tree set; reason: Lean convention; on every instance where (7.1) is feasible both sides are the book's real numbers
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 7.2, p. 260 (PDF p. 268); (7.1) p. 259; boxes pp. 253, 255; p. 256

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_subtourBound
import Definitions.Def_CombOpt_HeldKarp_Graph_heldKarpBound

namespace CombOpt.HeldKarp

/-- **Theorem 7.2 (Held–Karp 1970): the subtour bound equals the optimal Held–Karp bound
(corrected: loopless).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 7.2,
p. 260 (PDF p. 268): "The subtour bound is equal to the optimal Held-Karp bound." The subtour bound is
the optimal value of (7.1) (p. 259); the optimal Held–Karp bound is "the maximum Held-Karp bound over
all choices of node numbers" (p. 256), the Held–Karp bound being defined in the box on p. 255 for a
fixed node `v₁`.

For a finite loopless graph `G` (parallel edges allowed), real edge costs `c` and any node `v₁`:
`subtourBound G c = ⨆_{y : V → ℝ} heldKarpBound G c v₁ y` in `EReal`, and when the subtour bound is
not `⊤` this supremum is attained: some `y` has `heldKarpBound G c v₁ y = subtourBound G c`.

**Formalization Note.** Values in `EReal`: when (7.1) is infeasible both sides are `⊤`. The book's
"maximum" is the supremum over all real node numbers together with its attainment; attainment is
stated only when the subtour bound is not `⊤`, because when (7.1) is infeasible but `G` has 1-trees
every Held–Karp bound is real and the supremum `⊤` is not reached. The book's `G` is the complete
graph of §7.1 or "a graph" (boxes of §7.3); the statement covers every finite loopless graph, so it
specializes to the complete case. Loopless is a correction: on a triangle
`v₁ab` with costs 0 plus a loop at `a` of cost −1, the subtour bound is −1 (a loop is in no cut, so
it may take value 1) while every Held–Karp bound is 0. Completeness of `G`, metric costs and
`|V| ≥ 3` are not assumed. -/
theorem subtourBound_eq_iSup_heldKarpBound {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (hG : ∀ e : E, ¬ (G.ends e).IsDiag) (c : E → ℝ) (v₁ : V) :
    G.subtourBound c = ⨆ y : V → ℝ, G.heldKarpBound c v₁ y ∧
      (G.subtourBound c ≠ ⊤ → ∃ y : V → ℝ, G.heldKarpBound c v₁ y = G.subtourBound c) := by sorry

end CombOpt.HeldKarp
