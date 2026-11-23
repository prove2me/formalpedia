-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_Supplement_lemma_4_5
-- name    : BinaryExtForm.HypercubeRank.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:02:07.308805+00:00
-- url     : https://prove2.me/theorems/08a3c17d-fe23-4a76-bce1-e2cb0834670c
-- title:
--   Lemma 4.5, p. 10 — S = ⋃_j V(B(f_j)) and V(conv(S)) meet the relative interiors of the same edges of B
-- statement:
--   Let $B \subseteq \mathbb R \times [0,1]^d$ be a natural binarization (of $x$ in some range $\{0,\dots,k\}$, with $x$ an integer at every vertex of $B$). Let $\alpha_1, \dots, \alpha_\ell \in \mathbb Z$ and let $f_1, \dots, f_\ell$ be reals with $\alpha_j < f_j < \alpha_j + 1$. For a number $f$ write $B(f) = \{(x,y) \in B : x = f\}$, and put
--   $$S := \bigcup_{j \in [\ell]} V(B(f_j)).$$
--   An *edge* of $B$ is a $1$-dimensional face $[u,v]$, and its relative interior is the open segment $(u,v)$. Then
--
--   1. every point of $S$ lies in the relative interior of an edge of $B$;
--   2. every vertex of $\operatorname{conv}(S)$ lies in the relative interior of an edge of $B$;
--   3. for every edge $[u,v]$ of $B$, the open segment $(u,v)$ contains a point of $S$ if and only if it contains a vertex of $\operatorname{conv}(S)$.
--
--   Because relative interiors of distinct edges are disjoint, the minimum set of edges whose relative interiors cover a set $X$ is exactly the set of edges whose relative interior meets $X$; so items 1–3 say that the minimum cover of $S$ coincides with the minimum cover of $V(\operatorname{conv}(S))$.
--
--   In the proof of Theorem 4.6 the lemma lets the vertices of $\operatorname{conv}(\bigcup_j B_i(\bar x^j_i))$ be matched edge by edge with the vertices of the individual slices.
--
--   **Formalization Note.** Edges are the published `Hirsch.Adj B u v` ($u \ne v$ and the segment $[u,v]$ is an extreme subset of $B$) and relative interiors are `openSegment ℝ u v`. The range $k$ of $B$ is a free parameter, as in the paper, which says only "a natural binarization".
--
--   Differences from the source:
--   - reading: "the minimum set of 1-dimensional faces whose relative interiors cover S coincides with the minimum set … covering V(conv(S))" → both sets are covered by relative interiors of edges, and an edge's open segment meets S iff it meets V(conv(S)); reason: relative interiors of distinct edges are disjoint, so the minimum cover of a coverable set X is the set of edges whose relative interior meets X
--   - encoding: 1-dimensional faces and their relative interiors → `Hirsch.Adj B u v` and `openSegment ℝ u v`; reason: Lean conventions that change no instance
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 10, Lemma 4.5

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

namespace BinaryExtForm.HypercubeRank.Supplement
open BinaryExtForm.HypercubeRank
theorem lemma_4_5 {d k ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (α : Fin ℓ → ℤ) (f : Fin ℓ → ℝ)
    (hf : ∀ j, (α j : ℝ) < f j ∧ f j < α j + 1) :
    let S : Set (Fin (d + 1) → ℝ) := ⋃ j, Set.extremePoints ℝ (slice B (f j))
    (∀ s ∈ S, ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v) ∧
    (∀ s ∈ Set.extremePoints ℝ (convexHull ℝ S),
      ∃ u v, Hirsch.Adj B u v ∧ s ∈ openSegment ℝ u v) ∧
    ∀ u v, Hirsch.Adj B u v →
      ((∃ s ∈ S, s ∈ openSegment ℝ u v) ↔
        (∃ s ∈ Set.extremePoints ℝ (convexHull ℝ S), s ∈ openSegment ℝ u v)) := by sorry
end BinaryExtForm.HypercubeRank.Supplement
