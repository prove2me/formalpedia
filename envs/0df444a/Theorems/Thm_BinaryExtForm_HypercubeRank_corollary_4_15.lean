-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_corollary_4_15
-- name    : BinaryExtForm.HypercubeRank.corollary_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:38.905192+00:00
-- url     : https://prove2.me/theorems/363868e9-8f31-41c2-9b82-9f0b83033d3f
-- title:
--   Corollary 4.15, p. 12 — sk(π_y(B)) is a subgraph of sk(B) for integral B; isomorphic for affine B
-- statement:
--   Let $B \subseteq \mathbb R \times [0,1]^d$ be a binarization and let $\pi_y(B)$ be its projection onto the $y$-space.
--
--   1. If $B$ is integral, then $\operatorname{sk}(\pi_y(B))$ is a subgraph of $\operatorname{sk}(B)$ on the same vertex set: $\pi_y$ maps the vertices of $B$ bijectively onto the vertices of $\pi_y(B)$, and whenever $\pi_y(u), \pi_y(v)$ are adjacent in $\pi_y(B)$, the vertices $u, v$ are adjacent in $B$.
--   2. If $B$ is affine, then $\operatorname{sk}(B)$ and $\operatorname{sk}(\pi_y(B))$ are isomorphic: $\pi_y$ is a bijection between the vertex sets and $u, v$ are adjacent in $B$ if and only if $\pi_y(u), \pi_y(v)$ are adjacent in $\pi_y(B)$.
--
--   This is what lets the paper compare the skeleton of a hypercube binarization with the hypercube graph $G(B)$.
--
--   **Formalization Note.** "On the same vertex set" and "isomorphic" are made concrete through the map $\pi_y$ itself (`Set.BijOn yproj` on the vertex sets, plus the adjacency implication or equivalence). Adjacency is `Hirsch.Adj`.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 12, Corollary 4.15

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem corollary_4_15 {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B) :
    (IsIntegral B →
      Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) ∧
      ∀ u ∈ Set.extremePoints ℝ B, ∀ v ∈ Set.extremePoints ℝ B,
        Hirsch.Adj (yproj '' B) (yproj u) (yproj v) → Hirsch.Adj B u v) ∧
    (IsAffineBin B →
      Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) ∧
      ∀ u ∈ Set.extremePoints ℝ B, ∀ v ∈ Set.extremePoints ℝ B,
        (Hirsch.Adj (yproj '' B) (yproj u) (yproj v) ↔ Hirsch.Adj B u v)) := by sorry
end BinaryExtForm.HypercubeRank
