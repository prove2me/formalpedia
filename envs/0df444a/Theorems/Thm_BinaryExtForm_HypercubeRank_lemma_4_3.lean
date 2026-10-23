-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_3
-- name    : BinaryExtForm.HypercubeRank.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:24.383985+00:00
-- url     : https://prove2.me/theorems/a9bdabdc-c7a6-4cf7-a4e6-684eac235451
-- title:
--   Lemma 4.3, p. 9 — the vertices of a fractional slice B(f) lie on the α-edges of B
-- statement:
--   Let $B \subseteq \mathbb R \times [0,1]^d$ be a natural binarization of $x$ in the range $\{0, \dots, k\}$, let $\alpha \in \{0, \dots, k-1\}$ and let $\alpha < f < \alpha + 1$. Write $B(f) = \{(x,y) \in B : x = f\}$. Then the vertex set $V(B(f))$ consists of exactly one point $(\tilde x, \tilde y)$ in the relative interior of each $1$-dimensional face of $B$ whose endpoints $(x^u, y^u)$ and $(x^v, y^v)$ satisfy $x^u \le \alpha$ and $x^v \ge \alpha + 1$:
--   $$V(B(f)) = \{(\tilde x,\tilde y) : (\tilde x,\tilde y) \in \operatorname{relint}[u,v],\ \tilde x = f,\ [u,v] \text{ an edge of } B,\ x^u \le \alpha,\ x^v \ge \alpha+1\},$$
--   and each such edge contains exactly one point with $x = f$ in its relative interior.
--
--   The lemma describes the fractional vertices whose removal the rank of a binarization measures.
--
--   **Formalization Note.** An edge is `Hirsch.Adj B u v` (the segment $[u,v]$ is an extreme subset of $B$, $u \ne v$), and its relative interior is `openSegment ℝ u v`. The statement is the set equality together with the uniqueness of the point at height $x = f$ on each such edge.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 9, Lemma 4.3

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem lemma_4_3 {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (α : ℕ) (hα : α < k) (f : ℝ) (hf₁ : (α : ℝ) < f) (hf₂ : f < α + 1) :
    Set.extremePoints ℝ (slice B f) =
      {p | ∃ u v, Hirsch.Adj B u v ∧ u 0 ≤ α ∧ (α : ℝ) + 1 ≤ v 0 ∧
        p ∈ openSegment ℝ u v ∧ p 0 = f} ∧
    ∀ u v, Hirsch.Adj B u v → u 0 ≤ α → (α : ℝ) + 1 ≤ v 0 →
      ∃! p, p ∈ openSegment ℝ u v ∧ p 0 = f := by sorry
end BinaryExtForm.HypercubeRank
