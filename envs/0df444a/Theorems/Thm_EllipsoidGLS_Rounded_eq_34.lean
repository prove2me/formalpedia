-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_eq_34
-- name    : EllipsoidGLS.Rounded.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:48.651738+00:00
-- url     : https://prove2.me/theorems/c3cdd5a8-c52d-4d6e-bab0-faf254373900
-- title:
--   Proof of Theorem (2.4), (34), p. 177 — volume of the piece of the cone over the r-disc with apex y above the level t
-- statement:
--   Let $n\ge 2$, let $K\subseteq\mathbb{R}^n$ be convex, let $c\in\mathbb{R}^n$ be nonzero and $r>0$, and let $x_0\in\mathbb{R}^n$ be such that the $(n-1)$-dimensional disc
--   $$D=\{z\in\mathbb{R}^n : \|z-x_0\|\le r,\ c^{\mathsf T}z=c^{\mathsf T}x_0\}$$
--   lies in $K$. Let $y\in K$ with $\zeta:=c^{\mathsf T}y>c^{\mathsf T}x_0$, and let $t$ be a level with $c^{\mathsf T}x_0\le t\le\zeta$. Then
--   $$\frac{V_{n-1}\,r^{n-1}\,(\zeta-c^{\mathsf T}x_0)}{n\,\|c\|}\left(\frac{\zeta-t}{\zeta-c^{\mathsf T}x_0}\right)^{n}\le\mu\bigl(\{z\in K : c^{\mathsf T}z\ge t\}\bigr),$$
--   where $\mu$ is Lebesgue measure on $\mathbb{R}^n$, $V_{n-1}$ the volume of the Euclidean unit ball of $\mathbb{R}^{n-1}$ and $\|\cdot\|$ the Euclidean norm.
--
--   The left side is the volume of the part above the level $t$ of the cone with base $D$ and apex $y$, which lies in $K$ by convexity. In the proof of Theorem (2.4), $x_0=a_0$, $y$ maximizes $c^{\mathsf T}x$ over $K$, and $t=c^{\mathsf T}x_j$ for the best feasible centre $x_j$. When that level lies between the base and apex, the set on the right is $K_N$, and the inequality is the lower half of the volume squeeze.
--
--   **Formalization Note** The page states this for the run's data ($x_0=a_0$, $\zeta=\max_K c^{\mathsf T}x$, $t=c^{\mathsf T}x_j$, the set $K_N$); it is stated here as the geometric fact it uses, for any convex $K$ containing the disc, any $y\in K$ above the base and any level $t$ between the base and $y$. The restriction $c^{\mathsf T}x_0\le t\le\zeta$ is the range in which the page's expression is the volume of the cone piece: for $t>\zeta$ the piece is empty while the expression is positive for even $n$. A feasible centre can lie just outside $K$, so its objective level need not be at most $\zeta$; the remaining level cases need a separate argument in the goal proof. The exponents $n-1$ are natural-number subtractions, safe since $n\ge2$.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), pp. 176–177, proof of Theorem (2.4), (33)–(34)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem eq_34 {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (hK : Convex ℝ K)
    (c x₀ y : Fin n → ℝ) (hc : c ≠ 0) (r : ℝ) (hr : 0 < r)
    (hdisc : {z | euclNorm (z - x₀) ≤ r ∧ c ⬝ᵥ z = c ⬝ᵥ x₀} ⊆ K)
    (hy : y ∈ K) (hxy : c ⬝ᵥ x₀ < c ⬝ᵥ y)
    (t : ℝ) (ht₀ : c ⬝ᵥ x₀ ≤ t) (ht₁ : t ≤ c ⬝ᵥ y) :
    ENNReal.ofReal
        (unitBallVol (n - 1) * r ^ (n - 1) * (c ⬝ᵥ y - c ⬝ᵥ x₀) / (n * euclNorm c) *
          ((c ⬝ᵥ y - t) / (c ⬝ᵥ y - c ⬝ᵥ x₀)) ^ n) ≤
      MeasureTheory.volume {z | z ∈ K ∧ t ≤ c ⬝ᵥ z} := by sorry

end EllipsoidGLS.Rounded
