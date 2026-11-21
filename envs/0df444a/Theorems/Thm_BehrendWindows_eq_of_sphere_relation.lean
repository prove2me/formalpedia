-- Prove2me | Theorems.Thm_BehrendWindows_eq_of_sphere_relation
-- name    : BehrendWindows.eq_of_sphere_relation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:46:38.648956+00:00
-- url     : https://prove2.me/theorems/fa5a1dbc-a76f-4128-b503-cee2cb4be70f
-- title:
--   Three points on a sphere
-- statement:
--   Let $n\in\mathbb{N}$ and let $x,y,z\in\mathbb{N}^n$ be vectors of natural numbers with equal sums of squares,
--
--   $$\sum_{i} x_i^2=\sum_i y_i^2=\sum_i z_i^2 .$$
--
--   If natural numbers $p,q\ge 1$ satisfy the vector identity $p\,x+q\,z=(p+q)\,y$, then $x=z$.
--
--   Geometrically, $y$ is a strict convex combination of $x$ and $z$, and all three lie on one Euclidean sphere; strict convexity of the ball forces $x=z$. This is the geometric half of Behrend's construction, generalised from the midpoint relation $x+z=2y$ to arbitrary positive weights.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 1; generalises the strict-convexity step of F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, PNAS 32 (1946) 331-332, https://doi.org/10.1073/pnas.32.12.331

import Mathlib

namespace BehrendWindows

theorem eq_of_sphere_relation {n : ℕ} (x y z : Fin n → ℕ)
    (hx : ∑ i, x i ^ 2 = ∑ i, y i ^ 2) (hz : ∑ i, z i ^ 2 = ∑ i, y i ^ 2)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p • x + q • z = (p + q) • y) :
    x = z := by sorry

end BehrendWindows
