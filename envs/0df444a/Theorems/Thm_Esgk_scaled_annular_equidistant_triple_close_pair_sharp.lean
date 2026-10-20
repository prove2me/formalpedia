-- Prove2me | Theorems.Thm_Esgk_scaled_annular_equidistant_triple_close_pair_sharp
-- name    : Esgk.scaled_annular_equidistant_triple_close_pair_sharp
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:08:52.924256+00:00
-- url     : https://prove2.me/theorems/f7234574-5158-4c91-9114-6289b4972b5d
-- title:
--   Close pair among three equidistant points of a thin annulus, all radii
-- statement:
--   Let $c,p\in\mathbb R^2$, let $q_0,q_1,q_2\in\mathbb R^2$, and let $\rho,x,\sigma,t$ be real numbers with $\rho>0$, $\sigma>0$ and
--
--   $$
--   \sigma^2\le 1-x,\qquad x(\sigma+1)\le \sigma t .
--   $$
--
--   Assume that $\rho^2(1-x)\le |p-c|^2$, that each $q_i$ lies in the closed annulus
--
--   $$
--   \rho^2(1-x)\le |q_i-c|^2\le \rho^2 ,
--   $$
--
--   and that $q_0,q_1,q_2$ are equidistant from $p$, that is $|p-q_i|=|p-q_j|$ for all $i,j$. Then there are indices $i\ne j$ with
--
--   $$
--   |q_i-q_j|^2\le t\,\rho^2 .
--   $$
--
--   No bound on the common distance $|p-q_i|$ is assumed, and for $p$ only the lower annulus bound is assumed. The points $q_i$ need not be distinct.
--
--   For small $x$ the admissible threshold is close to $t=x(1+1/\sigma)\approx 2x$: three points of a thin annulus on any circle about such a point $p$ contain a pair at squared distance about $2x\rho^2$. It is the all-radius counterpart of the close-pair statement for circles of radius at most $\sqrt3\,\rho$.
--
--   **Formalization Note** Points are elements of `EuclideanSpace ℝ (Fin 2)`, the triple is a function `Fin 3 → ℝ²`, and all thresholds are stated for squared distances.
-- source:
--   Lean formalization by Adam McKenna (2026), declaration Esgk.scaled_annular_equidistant_triple_close_pair_sharp.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Esgk

namespace Esgk

theorem scaled_annular_equidistant_triple_close_pair_sharp
    (c p : Point) (q : Fin 3 → Point) {ρ x σ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (ht : x * (σ + 1) ≤ σ * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by sorry

end Esgk
