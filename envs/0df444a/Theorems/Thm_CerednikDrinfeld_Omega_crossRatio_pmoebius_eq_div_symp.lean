-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp
-- name    : CerednikDrinfeld.Omega.crossRatio_pmoebius_eq_div_symp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/7e62a1f1-72d6-5985-bbb7-38411bb7f112
-- title:
--   Cross ratio of Möbius images via 2× 2 determinant pairings
-- statement:
--   Let $K_0$ be a field, $K$ a field equipped with a $K_0$-algebra structure, and let $g_1,g_2,g_3,g_4 \in \mathrm{GL}_2(K_0)$. Let $w_1,w_2,w_3,w_4 \in K$ each lie in `upperHalfPlane K₀ K`, i.e. in the complement of the image of the structure map $K_0 \to K$. For $g \in \mathrm{GL}_2(K_0)$ and $w \in K$ write $P(g,w)$ for the vector in $K^2$ with entries $P(g,w)_0 = g_{00}w + g_{01}$ and $P(g,w)_1 = g_{10}w + g_{11}$, the matrix entries being transported to $K$ along the structure map; thus $P(g,w)$ is the image of the column $(w,1)$ under $g$. Let $z_i =$ `pmoebius K₀ (Matrix.ProjGenLinGroup.mk gᵢ) wᵢ`, the affine representative (with the point at infinity sent to $0$) of the action of the class of $g_i$ in $\mathrm{PGL}_2(K_0)$ on $w_i$ viewed in `OnePoint K`. The conclusion is the identity
--   $$\frac{(z_1-z_3)(z_2-z_4)}{(z_1-z_4)(z_2-z_3)} = \frac{\langle P_1,P_3\rangle\,\langle P_2,P_4\rangle}{\langle P_1,P_4\rangle\,\langle P_2,P_3\rangle},$$
--   where $P_i = P(g_i,w_i)$, $\langle P,Q\rangle = P_0Q_1 - P_1Q_0$, and the left-hand side is `crossRatio z₁ z₂ z₃ z₄`. No nonvanishing of the pairings is assumed: the identity is asserted with the field convention for division by zero.
--
--   This is the projective invariance of the cross ratio, written in homogeneous coordinates: the cross ratio of four Möbius images over the Drinfeld upper half plane is a quotient of determinant (symplectic) pairings of the transformed coordinate vectors. It is used to compute the valuation of such cross ratios in terms of the Bruhat–Tits tree, in [`CerednikDrinfeld.Omega.v_crossRatio_pmoebius_eq_zpow_walkOverlap`](thm.html#CerednikDrinfeld.Omega.v_crossRatio_pmoebius_eq_zpow_walkOverlap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_eq_div_symp
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K₀) {w₁ w₂ w₃ w₄ : K}
    (hw₁ : w₁ ∈ upperHalfPlane K₀ K) (hw₂ : w₂ ∈ upperHalfPlane K₀ K)
    (hw₃ : w₃ ∈ upperHalfPlane K₀ K) (hw₄ : w₄ ∈ upperHalfPlane K₀ K) :
    let P : GL (Fin 2) K₀ → K → Fin 2 → K := fun g w =>
      ![algebraMap K₀ K (g 0 0) * w + algebraMap K₀ K (g 0 1), algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)]
    crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
        (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄) =
      ((P g₁ w₁ 0 * P g₃ w₃ 1 - P g₁ w₁ 1 * P g₃ w₃ 0) * (P g₂ w₂ 0 * P g₄ w₄ 1 - P g₂ w₂ 1 * P g₄ w₄ 0)) /
      ((P g₁ w₁ 0 * P g₄ w₄ 1 - P g₁ w₁ 1 * P g₄ w₄ 0) * (P g₂ w₂ 0 * P g₃ w₃ 1 - P g₂ w₂ 1 * P g₃ w₃ 0)) := by sorry
