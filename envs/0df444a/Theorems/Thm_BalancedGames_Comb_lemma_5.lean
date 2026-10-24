-- Prove2me | Theorems.Thm_BalancedGames_Comb_lemma_5
-- name    : BalancedGames.Comb.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:25.358781+00:00
-- url     : https://prove2.me/theorems/d9ddea10-fb46-4218-a2ee-dfbdfb078a4e
-- title:
--   Lemma 5, p. 18 — distinct vertices v₁, v₂ of BG+(n) are non-adjacent iff v₁ + v₂ = v₃ + v₄ for other vertices; then 𝒟₃ ∪ 𝒟₄ = 𝒟₁ ∪ 𝒟₂, 𝒟₃ ∩ 𝒟₄ = 𝒟₁ ∩ 𝒟₂
-- statement:
--   Let $v_1\neq v_2$ be vertices of $\mathcal{BG}_+(n)$, with associated families $\mathcal D_1,\mathcal D_2$ (the family of a vertex $v$ is $\mathcal D(v)=\{S\neq\varnothing,N : v(S)=1\}$). Then:
--
--   1. $v_1,v_2$ are not adjacent (the segment $[v_1,v_2]$ is not an edge of $\mathcal{BG}_+(n)$) if and only if there are vertices $v_3,v_4$, each different from $v_1$ and from $v_2$, with
--   $$v_1+v_2=v_3+v_4 .$$
--   2. For any vertices $v_3,v_4$ with $v_1+v_2=v_3+v_4$, their families satisfy
--   $$\mathcal D_3\cup\mathcal D_4=\mathcal D_1\cup\mathcal D_2,\qquad \mathcal D_3\cap\mathcal D_4=\mathcal D_1\cap\mathcal D_2 .$$
--
--   Part 1 is the second condition of Definition 1 for $\mathcal{BG}_+(n)$; with Theorem 8 it makes $\mathcal{BG}_+(n)$ a combinatorial polytope.
--
--   **Formalization Note** Adjacency is the published `Hirsch.Adj`: the two points are distinct and the segment between them is an extreme subset (a face). Part 2 is asserted for every such pair $v_3,v_4$, not only for the pair produced in part 1.
--
--   Differences from the source:
--   - reading: "In addition, the associated collections $\mathcal D_3,\mathcal D_4$ satisfy …" (for the $v_3,v_4$ of the equivalence) → for every pair of vertices $v_3,v_4$ with $v_1+v_2=v_3+v_4$; reason: the sentence does not say which $v_3,v_4$; the stronger reading implies the weaker one and holds because vertices are 0-1-valued.
--   - generalization: $N=\{1,\dots,n\}$ with $n\ge1$ implicit → every $n\in\mathbb N$; reason: at $n=0$ the polytope is empty and the statement is vacuous; it specializes to the paper's for $n\ge1$.
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves vertices, edges and sums.
--   - encoding: balanced by (4) → nonempty core; reason: p. 4 identifies the two (Theorem 1).
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 18, Lemma 5

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Lemma 5** (p. 18). Let `v₁ ≠ v₂` be vertices of `BG+(n)` with families `𝒟₁, 𝒟₂`.
(a) `v₁, v₂` are not adjacent iff there are vertices `v₃, v₄` distinct from `v₁, v₂` with
`v₁ + v₂ = v₃ + v₄`.
(b) For any vertices `v₃, v₄` with `v₁ + v₂ = v₃ + v₄`, their families satisfy
`𝒟₃ ∪ 𝒟₄ = 𝒟₁ ∪ 𝒟₂` and `𝒟₃ ∩ 𝒟₄ = 𝒟₁ ∩ 𝒟₂`. -/
theorem lemma_5 (n : ℕ) (v₁ v₂ : Game n)
    (h₁ : v₁ ∈ Set.extremePoints ℝ (BGplus n)) (h₂ : v₂ ∈ Set.extremePoints ℝ (BGplus n))
    (h₁₂ : v₁ ≠ v₂) :
    (¬ Hirsch.Adj (BGplus n) v₁ v₂ ↔
      ∃ v₃ ∈ Set.extremePoints ℝ (BGplus n), ∃ v₄ ∈ Set.extremePoints ℝ (BGplus n),
        v₃ ≠ v₁ ∧ v₃ ≠ v₂ ∧ v₄ ≠ v₁ ∧ v₄ ≠ v₂ ∧ v₁ + v₂ = v₃ + v₄) ∧
    (∀ v₃ ∈ Set.extremePoints ℝ (BGplus n), ∀ v₄ ∈ Set.extremePoints ℝ (BGplus n),
      v₁ + v₂ = v₃ + v₄ →
        coalitions v₃ ∪ coalitions v₄ = coalitions v₁ ∪ coalitions v₂ ∧
        coalitions v₃ ∩ coalitions v₄ = coalitions v₁ ∩ coalitions v₂) := by sorry

end BalancedGames.Comb
