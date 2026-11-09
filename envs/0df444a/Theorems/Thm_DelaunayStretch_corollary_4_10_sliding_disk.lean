-- Prove2me | Theorems.Thm_DelaunayStretch_corollary_4_10_sliding_disk
-- name    : DelaunayStretch.corollary_4_10_sliding_disk
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:57:12.74397+00:00
-- url     : https://prove2.me/theorems/d2c58f50-e2ac-4104-adc2-a78169a850e3
-- title:
--   Corollary 4.10 — the potential does not increase along the pencil
-- statement:
--   Let $U\in\mathbb R$ and let $H$ satisfy (H0) and (H4) at level $U$. Let $G=[a_G,b_G]$ be a segment with $y(a_G)>0>y(b_G)$, let $\delta\in[-|G|,|G|]$, and let $s(X)=(O(X),G,\delta)$ be the gate states along the pencil of $G$. Then
--
--   $$
--   W_{H,U}(s(X_2))\le W_{H,U}(s(X_1))\qquad\text{whenever }X_1<X_2 .
--   $$
--
--   This pays for the second stage of a step and for the initial pair in the proof of Theorem 4.7.
--
--   **Formalization Note** "Satisfies (H0) and (H4) at level $U$" is: for some piecewise $C^1$ structure, (H0) holds and (H4) holds with respect to it.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Corollary 4.10, p.28

import Mathlib
import Definitions.Def_DelaunayStretch_pencilDisk
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Corollary 4.10 (Sliding the disk along a pencil)** (p.28). Let `U ∈ ℝ`, and let `H`
satisfy (H0) and (H4) at level `U`. Let `G = [aG, bG]` be a segment with `y(aG) > 0 > y(bG)`,
let `δ ∈ [−|G|, |G|]`, and let `s(X) = (O(X), G, δ)`, `X ∈ ℝ`, be the gate states along the
pencil of `G`, as in Lemma 4.4(2). Then `W_{H,U}(s(X₂)) ≤ W_{H,U}(s(X₁))` whenever `X₁ < X₂`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Corollary 4.10, p.28.

**Formalization Note** "Satisfies (H0) and (H4) at level `U`" is: for some piecewise `C¹`
structure `P` of `H`, (H0) holds and (H4) holds with respect to `P`. -/
theorem corollary_4_10_sliding_disk (U : ℝ) (H : R4 → ℝ)
    (hH : ∃ P : PiecewiseC1 H, CondH0 H ∧ CondH4 U P) (aG bG : ℂ) (ha : 0 < aG.im)
    (hb : bG.im < 0) (δ : ℝ) (hδ : |δ| ≤ dist aG bG) (X₁ X₂ : ℝ) (hX : X₁ < X₂) :
    potential H U (pencilState aG bG δ X₂) ≤ potential H U (pencilState aG bG δ X₁) := by sorry

end DelaunayStretch
