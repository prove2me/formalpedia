-- Prove2me | Theorems.Thm_ChvatalPolytopes_Separation_union_isDefiningSystem
-- name    : ChvatalPolytopes.Separation.union_isDefiningSystem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:18:26.141067+00:00
-- url     : https://prove2.me/theorems/d3591128-e38d-49b6-b7fc-125a38b52024
-- title:
--   Theorem 4.1 — defining systems glue along a complete intersection
-- statement:
--   For graphs $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ set $G_1\cap G_2=(V_1\cap V_2,E_1\cap E_2)$ and $G_1\cup G_2=(V_1\cup V_2,E_1\cup E_2)$. Suppose $G_1\cap G_2$ is complete. Let
--   $$-x_u\le0\ (u\in V_1),\qquad \sum_{u\in V_1}a_{iu}x_u\le b_i\ (i\in J_1)\tag{4.1}$$
--   be a defining linear system of $P(G_1)$, and
--   $$-x_u\le0\ (u\in V_2),\qquad \sum_{u\in V_2}a_{iu}x_u\le b_i\ (i\in J_2)\tag{4.2}$$
--   a defining linear system of $P(G_2)$. Then the union of (4.1) and (4.2) is a defining linear system of $P(G_1\cup G_2)$: a vector $x\in\mathbb R^{V_1\cup V_2}$ lies in $P(G_1\cup G_2)$ if and only if $x\ge0$, its restriction to $V_1$ satisfies the rows $J_1$ and its restriction to $V_2$ satisfies the rows $J_2$.
--
--   Gluing two graphs along a clique therefore needs no new inequalities: a linear description of the stable set polytope of the glued graph is obtained by putting together descriptions of the two pieces. This is the half of Corollary 4.3 that says a clique cutset produces no facet involving all vertices.
--
--   **Formalization Note** The glued graph $G=G_1\cup G_2$ is a `SimpleGraph` on a finite type $V$ with finsets $V_1\cup V_2=V$; $G_1$, $G_2$ are the subgraphs of $G$ induced on $V_1$, $V_2$. "$G_1\cap G_2$ complete" becomes: $V_1\cap V_2$ is a clique of $G$, and no edge of $G$ joins $V_1-V_2$ to $V_2-V_1$ (every edge of $G_1\cup G_2$ lies in $V_1$ or in $V_2$). These hypotheses are equivalent to the paper's, and under them the induced subgraphs are exactly $G_1$, $G_2$. The systems (4.1), (4.2) have real coefficients indexed by finite types $J_1$, $J_2$; the union's rows are read on $V$ by restricting $x$ to $V_1$ and $V_2$ (equivalently, extending coefficients by $0$).
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 141, Theorem 4.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope

namespace ChvatalPolytopes.Separation

/-- **Theorem 4.1** (Chvátal 1975, p. 141). Let `G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` be graphs such
that `G₁ ∩ G₂ = (V₁ ∩ V₂, E₁ ∩ E₂)` is complete. Let (4.1)
`−x_u ≤ 0 (u ∈ V₁)`, `Σ (a_{iu} x_u : u ∈ V₁) ≤ b_i (i ∈ J₁)`
be a defining linear system of `P(G₁)` and (4.2)
`−x_u ≤ 0 (u ∈ V₂)`, `Σ (a_{iu} x_u : u ∈ V₂) ≤ b_i (i ∈ J₂)`
a defining linear system of `P(G₂)`. Then the union of (4.1) and (4.2) is a defining linear
system of `P(G₁ ∪ G₂)`, where `G₁ ∪ G₂ = (V₁ ∪ V₂, E₁ ∪ E₂)`.

Encoding: `G` is the graph `G₁ ∪ G₂` on the vertex type `V = V₁ ∪ V₂` (`hcover`); `G₁` and `G₂`
are the subgraphs of `G` induced on `V₁` and `V₂`. "`G₁ ∩ G₂` is complete" is `hclique`
(`V₁ ∩ V₂` is a clique of `G`), and `G = G₁ ∪ G₂` forces `hsep` (no edge of `G` joins
`V₁ − V₂` to `V₂ − V₁`). Under these hypotheses the induced subgraphs are exactly the paper's
`G₁, G₂`. The rows of (4.1), (4.2) are read on `V` by restricting `x` to `V₁`, `V₂`
(equivalently, coefficients are extended by `0`); the nonnegativity rows of the union are
`−x_u ≤ 0` for all `u ∈ V₁ ∪ V₂ = V`. -/
theorem union_isDefiningSystem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hcover : V₁ ∪ V₂ = Finset.univ)
    (hclique : G.IsClique ((V₁ ∩ V₂ : Finset V) : Set V))
    (hsep : ∀ u v, u ∈ V₁ → u ∉ V₂ → v ∈ V₂ → v ∉ V₁ → ¬ G.Adj u v)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → ↥(V₁ : Set V) → ℝ) (b₁ : J₁ → ℝ)
    (a₂ : J₂ → ↥(V₂ : Set V) → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : ↥(V₁ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} =
      Shared.stablePolytope (G.induce (V₁ : Set V)))
    (h₂ : {x : ↥(V₂ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₂ i u * x u ≤ b₂ i} =
      Shared.stablePolytope (G.induce (V₂ : Set V))) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ (∀ i, ∑ u : ↥(V₁ : Set V), a₁ i u * x u ≤ b₁ i) ∧
        (∀ i, ∑ u : ↥(V₂ : Set V), a₂ i u * x u ≤ b₂ i)} = Shared.stablePolytope G := by sorry

end ChvatalPolytopes.Separation
