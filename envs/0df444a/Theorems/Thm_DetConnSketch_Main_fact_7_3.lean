-- Prove2me | Theorems.Thm_DetConnSketch_Main_fact_7_3
-- name    : DetConnSketch.Main.fact_7_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:27.406036+00:00
-- url     : https://prove2.me/theorems/fed12fa6-8e0d-4add-85f0-75994c4018ac
-- title:
--   Fact 7.3 — a unit-diagonal PSD matrix supported on the edges of $H$ gives $\chi(H)\ge \mathbf 1^\top M\mathbf 1/N$
-- statement:
--   Let $H$ be a graph on $N$ vertices and let $M \in \mathbb R^{N\times N}$ be positive semidefinite with $M_{xx} = 1$ for every vertex $x$ and $M_{xy} = 0$ whenever $x \ne y$ and $xy$ is not an edge of $H$. Then
--   $$\chi(H) \ge \frac{\mathbf 1^\top M \mathbf 1}{N} = \frac{1}{N}\sum_{x,y} M_{xy}.$$
--
--   This is Lovász's bound (Theorem 4 of [Lov79]); the paper applies it to the universal graph with the matrix of Eq. (4).
--
--   Differences from the source:
--   - encoding: χ(H) ≥ 1ᵀM1/N → for every c, H.Colorable c → (∑_{x,y} M x y)/N ≤ c; reason: χ(H) is the least such c; avoids ℕ∞
--   - encoding: vertex set [N] → a Fintype V with N = Fintype.card V; reason: any labelling of the N vertices
--   - generalization: the quotient 1ᵀM1/N on a nonempty graph → also permits an empty finite vertex type, with Lean division 0/0 = 0; reason: the extra empty instance is 0 ≤ c; restricting to N ≥ 1 recovers every source instance without changing the bound
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 42 (PDF 46), Fact 7.3

import Mathlib

namespace DetConnSketch.Main

/-- Fact 7.3 (Lovász): let `H` be a graph on `N` vertices and `M` a real positive semidefinite
`N × N` matrix with `M_xx = 1` for every `x` and `M_xy = 0` whenever `x ≠ y` and `xy` is not an
edge of `H`. Then `χ(H) ≥ 1ᵀ M 1 / N`: every proper colouring of `H` with `c` colours has
`1ᵀ M 1 / N ≤ c`. -/
theorem fact_7_3 {V : Type} [Fintype V] (H : SimpleGraph V) (M : Matrix V V ℝ)
    (hpsd : M.PosSemidef) (hdiag : ∀ x, M x x = 1)
    (hsupp : ∀ x y, x ≠ y → ¬ H.Adj x y → M x y = 0) :
    ∀ c : ℕ, H.Colorable c → (∑ x, ∑ y, M x y) / (Fintype.card V : ℝ) ≤ c := by sorry

end DetConnSketch.Main
