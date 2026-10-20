-- Prove2me | Theorems.Thm_Esgk_scaled_annular_equidistant_triple_close_pair_small_radius
-- name    : Esgk.scaled_annular_equidistant_triple_close_pair_small_radius
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:05:39.063618+00:00
-- url     : https://prove2.me/theorems/879d2647-583e-4321-a7a0-8c868cb33ee3
-- title:
--   Close pair among three equidistant points of a thin annulus, radius at most $\sqrt{3}\,\rho$
-- statement:
--   Let $c,p\in\mathbb R^2$, let $q_0,q_1,q_2\in\mathbb R^2$, and let $\rho,x,\sigma,\kappa,\gamma,t$ be real numbers such that
--
--   1. $\rho>0$, $\sigma>0$, $\sigma^2\le 1-x$, $\kappa>0$, $\gamma\ge 0$ and $\gamma^2<1$;
--   2. $1\le 2\sigma\gamma\kappa$, $3\le 4\gamma^2\sigma^2$, $\kappa^2x+1\le 2\gamma\kappa$ and $(3+x)^2\le 12\gamma^2$;
--   3. $4\kappa^2x^2\le t$ and $x^2\le 4\sigma^2(1-\gamma^2)\,t$.
--
--   Assume that $p,q_0,q_1,q_2$ lie in the closed annulus
--
--   $$
--   \rho^2(1-x)\le |z-c|^2\le \rho^2 ,
--   $$
--
--   that $q_0,q_1,q_2$ are equidistant from $p$, that is $|p-q_i|=|p-q_j|$ for all $i,j$, and that $|p-q_i|^2\le 3\rho^2$. Then there are indices $i\ne j$ with
--
--   $$
--   |q_i-q_j|^2\le t\,\rho^2 .
--   $$
--
--   The points $q_i$ need not be distinct.
--
--   This is a scale-free close-pair statement for three points of a thin annulus on a circle of radius at most $\sqrt3\,\rho$ about a point of the annulus. All parameter conditions are polynomial inequalities, so for rational parameters they can be checked by exact arithmetic. With $c$ the centroid of a point configuration and $\rho$ its outer radius, it gives close pairs among configuration points that lie on a common circle about another configuration point.
--
--   **Formalization Note** Points are elements of `EuclideanSpace ℝ (Fin 2)`, the triple is a function `Fin 3 → ℝ²`, and all thresholds are stated for squared distances.
-- source:
--   Lean formalization by Adam McKenna (2026), declaration Esgk.scaled_annular_equidistant_triple_close_pair_small_radius.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Esgk

namespace Esgk

theorem scaled_annular_equidistant_triple_close_pair_small_radius
    (c p : Point) (q : Fin 3 → Point) {ρ x σ κ γ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hγ1 : γ ^ 2 < 1) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (ht1 : 4 * κ ^ 2 * x ^ 2 ≤ t) (ht2 : x ^ 2 ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2) (hp1 : dist p c ^ 2 ≤ ρ ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hr : ∀ i, dist p (q i) ^ 2 ≤ 3 * ρ ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by sorry

end Esgk
