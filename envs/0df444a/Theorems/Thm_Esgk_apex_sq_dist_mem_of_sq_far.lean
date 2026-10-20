-- Prove2me | Theorems.Thm_Esgk_apex_sq_dist_mem_of_sq_far
-- name    : Esgk.apex_sq_dist_mem_of_sq_far
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:11:07.22883+00:00
-- url     : https://prove2.me/theorems/4048c0f8-0d0a-4939-9cf6-0e059be6a9dc
-- title:
--   Apex radius of a far pair in a thin annulus
-- statement:
--   Let $c,z,a,b\in\mathbb R^2$ and let $\rho>0$ and $x$ be real numbers. Assume that $z$, $a$ and $b$ lie in the closed annulus
--
--   $$
--   \rho^2(1-x)\le |w-c|^2\le \rho^2 ,
--   $$
--
--   that $|a-b|^2>3\rho^2$, and that $z$ is equidistant from $a$ and $b$, that is $|z-a|=|z-b|$. Then
--
--   $$
--   \rho^2(1-2x)<|z-a|^2<3\rho^2 .
--   $$
--
--   A pair of points of a thin annulus at distance more than $\sqrt3\,\rho$ is therefore seen from every equidistant point of the annulus at a squared radius in the fixed window $(\rho^2(1-2x),\,3\rho^2)$. This places the apexes of far pairs in apex-counting arguments.
--
--   **Formalization Note** Points are elements of `EuclideanSpace ℝ (Fin 2)`; the annulus bounds are stated for squared distances.
-- source:
--   Lean formalization by Adam McKenna (2026), declaration Esgk.apex_sq_dist_mem_of_sq_far.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Esgk

namespace Esgk

theorem apex_sq_dist_mem_of_sq_far {c z a b : Point} {ρ x : ℝ} (hρ : 0 < ρ)
    (hz : ρ ^ 2 * (1 - x) ≤ dist z c ^ 2) (hz1 : dist z c ^ 2 ≤ ρ ^ 2)
    (ha : ρ ^ 2 * (1 - x) ≤ dist a c ^ 2) (ha1 : dist a c ^ 2 ≤ ρ ^ 2)
    (hb : ρ ^ 2 * (1 - x) ≤ dist b c ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2)
    (hab : 3 * ρ ^ 2 < dist a b ^ 2) (heq : dist z a = dist z b) :
    ρ ^ 2 * (1 - 2 * x) < dist z a ^ 2 ∧ dist z a ^ 2 < 3 * ρ ^ 2 := by sorry

end Esgk
