-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_10
-- name    : BallPolyApprox.VertexBudget.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:56:25.103198+00:00
-- url     : https://prove2.me/theorems/4172cc57-d5ea-41a1-bc8b-e860699a7074
-- title:
--   Lemma 10 — exact first two moments of $Q_d$ and $\mathrm{Var}(Q_d)\le 12/(d-1)^3$
-- statement:
--   For every $d\ge2$, the angular variable $Q_d$ of (21) satisfies
--   $$q_d:=\mathbb EQ_d=\frac{2(d-1)}{d(d+1)}\ (22),\qquad \mathbb EQ_d^2=\frac{4(d-1)(d+7)}{(d+1)^2(d+2)(d+3)}\ (23),$$
--   $$\mathrm{Var}(Q_d)=\frac{4(d-1)(3d^2-d+6)}{d^2(d+1)^2(d+2)(d+3)}\le\frac{12}{(d-1)^3}\ (24).$$
--   These are the moments that place $Q_d$ at $2/d$ with fluctuations of order $d^{-3/2}$.
--
--   Differences from the source: none.
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 10, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer
import Definitions.Def_BallPolyApprox_VertexBudget_AngularLaw

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 10 (p. 13, PDF 15): for every `d ≥ 2`, the angular variable `Q_d` of (21) has
`E Q_d = 2(d−1)/(d(d+1))` (22), `E Q_d² = 4(d−1)(d+7)/((d+1)²(d+2)(d+3))` (23), and
`Var(Q_d) = 4(d−1)(3d²−d+6)/(d²(d+1)²(d+2)(d+3)) ≤ 12/(d−1)³` (24). -/
theorem lemma_10 (d : ℕ) (hd : 2 ≤ d) :
    ∫ q, q ∂QLaw d = 2 * ((d : ℝ) - 1) / ((d : ℝ) * ((d : ℝ) + 1)) ∧
    ∫ q, q ^ 2 ∂QLaw d =
      4 * ((d : ℝ) - 1) * ((d : ℝ) + 7) /
        (((d : ℝ) + 1) ^ 2 * ((d : ℝ) + 2) * ((d : ℝ) + 3)) ∧
    ∫ q, (q - ∫ q', q' ∂QLaw d) ^ 2 ∂QLaw d =
      4 * ((d : ℝ) - 1) * (3 * (d : ℝ) ^ 2 - (d : ℝ) + 6) /
        ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) + 2) * ((d : ℝ) + 3)) ∧
    ∫ q, (q - ∫ q', q' ∂QLaw d) ^ 2 ∂QLaw d ≤ 12 / ((d : ℝ) - 1) ^ 3 := by sorry

end BallPolyApprox.VertexBudget
