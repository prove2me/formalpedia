-- Prove2me | Theorems.Thm_ChvatalPolytopes_Substitution_substitution_defining_system
-- name    : ChvatalPolytopes.Substitution.substitution_defining_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:59:03.958694+00:00
-- url     : https://prove2.me/theorems/fd4426c2-4986-4e16-8bd1-00bc3f3fb742
-- title:
--   Theorem 5.1 — a defining linear system of $P(G)$ after substituting $G_2$ for a vertex of $G_1$
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be finite graphs with $V_1\cap V_2=\emptyset$ and $V_2\neq\emptyset$. For $k\in\{1,2\}$ let
--   $$-x_u\le 0\quad(u\in V_k),\qquad \sum_{u\in V_k}a_{iu}x_u\le b_i\quad(i\in J_k)$$
--   be a defining linear system of the stable set polytope $P(G_k)$, with $J_1,J_2$ finite and all coefficients real. Let $v$ be a vertex of $G_1$, let $G$ be the graph obtained from $G_1$ by substituting $G_2$ for $v$, and for each $i\in J_1$ set $a^+_{iv}=\max\{a_{iv},0\}$. Then
--   $$\begin{aligned}
--   -x_u&\le 0 && (u\in V_2\cup(V_1-\{v\})),\\
--   a^+_{iv}\sum_{u\in V_2}a_{ju}x_u+b_j\sum_{u\in V_1-\{v\}}a_{iu}x_u&\le b_ib_j && (i\in J_1,\ j\in J_2)
--   \end{aligned}\tag{5.1}$$
--   is a defining linear system of $P(G)$: a vector $x\in\mathbb R^{V_2\cup(V_1-\{v\})}$ satisfies (5.1) if and only if $x\in P(G)$.
--
--   The theorem turns a polyhedral description of the two pieces into one of the composite graph, row by row. Specialisations give defining systems for duplication of a vertex, for joins (Corollary 5.2) and for lexicographic products.
--
--   **Formalization Note** Vertices of $G$ are the disjoint sum $\{u\in V_1:u\ne v\}\oplus V_2$, so $V_1\cap V_2=\emptyset$ is built in. "Defining linear system" is the set equality between the solution set, nonnegativity rows included, and $P(G)=\operatorname{conv}S(G)$. The hypothesis $V_2\neq\emptyset$ is implicit in the paper (its graphs follow Harary and have nonempty vertex sets, and the proof picks a vertex $w$ of $G_2$) and is made explicit: with $V_2=\emptyset$, $J_2=\emptyset$ and $V_1\neq\{v\}$ the system (5.1) reduces to $x\ge0$ and the statement fails.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 145, Theorem 5.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Theorem 5.1** (Chvátal 1975, p. 145). Let `G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` be graphs with
`V₁ ∩ V₂ = ∅`. For `k ∈ {1, 2}`, let
`−x_u ≤ 0 (u ∈ V_k)`, `Σ (a_{iu} x_u : u ∈ V_k) ≤ b_i (i ∈ J_k)`
be a defining linear system of `P(G_k)`. Let `v` be a vertex of `G₁` and let `G` be the graph
obtained from `G₁` by substituting `G₂` for `v`. For each `i ∈ J₁`, set
`a⁺_{iv} = max {a_{iv}, 0}`. Then
`−x_u ≤ 0 (u ∈ V₂ ∪ (V₁ − {v}))`,
`a⁺_{iv} Σ (a_{ju} x_u : u ∈ V₂) + b_j Σ (a_{iu} x_u : u ∈ V₁ − {v}) ≤ b_i b_j
(i ∈ J₁, j ∈ J₂)` (5.1)
is a defining linear system of `P(G)`, i.e. its solution set equals `P(G) = conv S(G)`.

Conventions: vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `V₁ − {v}`, `inr` = `V₂`), so
`V₁ ∩ V₂ = ∅` is built in; `J₁`, `J₂` are finite index types, coefficients real; "defining linear
system of `P(G_k)`" is the set equality `h₁`/`h₂`.

**Implicit hypothesis made explicit:** `[Nonempty V₂]`. The paper's graphs have nonempty vertex
sets (Harary), and its proof picks "an arbitrary vertex `w` of `G₂`" (p. 148). With `V₂ = ∅` the
statement is false (take `J₂ = ∅` and `V₁ ≠ {v}`: then (5.1) is only `x ≥ 0`). -/
theorem substitution_defining_system {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → V₁ → ℝ) (b₁ : J₁ → ℝ) (a₂ : J₂ → V₂ → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : V₁ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} = Shared.stablePolytope G₁)
    (h₂ : {x : V₂ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ j, ∑ u, a₂ j u * x u ≤ b₂ j} = Shared.stablePolytope G₂)
    (v : V₁) :
    {x : {u : V₁ // u ≠ v} ⊕ V₂ → ℝ |
        (∀ u, 0 ≤ x u) ∧
        ∀ i j, max (a₁ i v) 0 * ∑ u : V₂, a₂ j u * x (.inr u)
          + b₂ j * ∑ w : {u : V₁ // u ≠ v}, a₁ i w * x (.inl w) ≤ b₁ i * b₂ j} =
      Shared.stablePolytope (substitute G₁ v G₂) := by sorry

end ChvatalPolytopes.Substitution
