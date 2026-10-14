-- Prove2me | Theorems.Thm_DbarRegularity_volume_ball_mul
-- name    : DbarRegularity.volume_ball_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:19:48.795104+00:00
-- url     : https://prove2.me/theorems/b4c3df44-dd6e-4321-9bc6-a0e389216d70
-- title:
--   Scaling of the Lebesgue measure of balls in R^d
-- statement:
--   Let $m$ be Lebesgue measure on $\mathbb{R}^d$ and $B(x,r)$ the open ball of centre $x$ and radius $r$. For every $x\in\mathbb{R}^d$, every $r>0$ and every $c>0$,
--   $$m\big(B(x,cr)\big)=c^d\,m\big(B(x,r)\big).$$
--
--   This is the scaling law for the volume of balls in $\mathbb{R}^d$. It holds for every dimension $d\ge0$ and every centre.
--
--   **Formalization Note.** The space is `EuclideanSpace ℝ (Fin d)` with `volume`; the factor $c^d$ is `ENNReal.ofReal c ^ d`, and both sides are in `ℝ≥0∞`.
-- source:
--   Auxiliary statement for E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (b), p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- Lebesgue measure of a ball in `ℝ^d` scales as the `d`-th power of the radius:
`|B(x, c r)| = c^d |B(x, r)|` for `r, c > 0`. -/
theorem volume_ball_mul (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hc : 0 < c) :
    volume (ball x (c * r)) = ENNReal.ofReal c ^ d * volume (ball x r) := by sorry

end DbarRegularity
