-- Prove2me | Theorems.Thm_ChvatalPolytopes_Substitution_substitution_system_valid
-- name    : ChvatalPolytopes.Substitution.substitution_system_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:57:27.425831+00:00
-- url     : https://prove2.me/theorems/1775547d-5a5e-4b99-b52b-decbcf91e276
-- title:
--   Theorem 5.1, first step — every $x\in S(G)$ satisfies (5.1)
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be finite graphs with disjoint vertex sets. For $k\in\{1,2\}$ let
--   $$-x_u\le 0\quad(u\in V_k),\qquad \sum_{u\in V_k}a_{iu}x_u\le b_i\quad(i\in J_k)$$
--   be a defining linear system of $P(G_k)$, with $J_1,J_2$ finite and all coefficients real. Let $v\in V_1$, let $G$ be the graph obtained from $G_1$ by substituting $G_2$ for $v$, and put $a^+_{iv}=\max\{a_{iv},0\}$ for $i\in J_1$.
--
--   Then every $x\in S(G)$ satisfies $x_u\ge 0$ for all $u\in V_2\cup(V_1-\{v\})$ and
--   $$a^+_{iv}\sum_{u\in V_2}a_{ju}x_u\;+\;b_j\sum_{u\in V_1-\{v\}}a_{iu}x_u\;\le\; b_ib_j\qquad(i\in J_1,\ j\in J_2).\tag{5.1}$$
--
--   This is the inclusion $P(G)\subseteq\{x : x \text{ satisfies } (5.1)\}$, one half of Theorem 5.1; the paper leaves its verification to the reader.
--
--   **Formalization Note** Vertices of $G$ are the disjoint sum $\{u\in V_1:u\neq v\}\oplus V_2$. "Defining linear system of $P(G_k)$" is the set equality between the solution set (nonnegativity rows included) and $P(G_k)=\operatorname{conv}S(G_k)$. The hypothesis $V_2\neq\emptyset$ that the goal theorem needs is not required for this half and is not assumed.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 145, §5, proof of Theorem 5.1 (first sentence)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Validity of (5.1)** (Chvátal 1975, §5, p. 145, proof of Theorem 5.1: "each `x ∈ S(G)` is a
solution of (5.1)").

Hypotheses of Theorem 5.1: for `k ∈ {1, 2}` the system `−x_u ≤ 0 (u ∈ V_k)`,
`Σ (a_{iu} x_u : u ∈ V_k) ≤ b_i (i ∈ J_k)` is a defining linear system of `P(G_k)`; `v` is a
vertex of `G₁`, `G` is obtained from `G₁` by substituting `G₂` for `v`, and
`a⁺_{iv} = max {a_{iv}, 0}`. Conclusion: every `x ∈ S(G)` satisfies
`x_u ≥ 0 (u ∈ V₂ ∪ (V₁ − {v}))` and, for all `i ∈ J₁`, `j ∈ J₂`,
`a⁺_{iv} Σ (a_{ju} x_u : u ∈ V₂) + b_j Σ (a_{iu} x_u : u ∈ V₁ − {v}) ≤ b_i b_j`.

Vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `V₁ − {v}`, `inr` = `V₂`). The hypothesis
`V₂ ≠ ∅` of the goal theorem is not needed for this half and is not assumed. -/
theorem substitution_system_valid {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → V₁ → ℝ) (b₁ : J₁ → ℝ) (a₂ : J₂ → V₂ → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : V₁ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} = Shared.stablePolytope G₁)
    (h₂ : {x : V₂ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ j, ∑ u, a₂ j u * x u ≤ b₂ j} = Shared.stablePolytope G₂)
    (v : V₁) :
    ∀ x ∈ Shared.stableVectors (substitute G₁ v G₂),
      (∀ u, 0 ≤ x u) ∧
      ∀ i j, max (a₁ i v) 0 * ∑ u : V₂, a₂ j u * x (.inr u)
          + b₂ j * ∑ w : {u : V₁ // u ≠ v}, a₁ i w * x (.inl w) ≤ b₁ i * b₂ j := by sorry

end ChvatalPolytopes.Substitution
