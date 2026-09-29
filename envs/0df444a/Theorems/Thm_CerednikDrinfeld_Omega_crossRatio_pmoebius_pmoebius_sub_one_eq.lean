-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq
-- name    : CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/0f770681-1dc6-5b25-bef1-054966af20ef
-- title:
--   Cross-ratio of Möbius images: the defect from 1
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure, let $g \in \mathrm{GL}_2(K_0)$ with entries $g_{00}, g_{01}, g_{10}, g_{11}$, and let $z, z_0, a, b \in K$. Assume $a$ and $b$ lie in `upperHalfPlane K₀ K`, that is, in the complement of the image of the structure map $K_0 \to K$, and write $\alpha,\beta,c,d$ for the images in $K$ of $g_{00},g_{01},g_{10},g_{11}$. Assume further that the two quantities $\Phi := z(cb+d)-(\alpha b+\beta)$ and $\Phi_0 := z_0(ca+d)-(\alpha a+\beta)$ are non-zero. Then, with $g$ acting through its class in $\mathrm{PGL}_2(K_0)$ on $\mathbb{P}^1(K)$ and `pmoebius` denoting the resulting map on $K$ (the point at infinity being sent to $0$ by `toAffine`), the cross-ratio $$\frac{(z - g\!\cdot\! a)(z_0 - g\!\cdot\! b)}{(z - g\!\cdot\! b)(z_0 - g\!\cdot\! a)} - 1 = \frac{(z-z_0)(a-b)\,\det g}{\Phi\,\Phi_0},$$ where $\det g = g_{00}g_{11} - g_{01}g_{10}$ is mapped into $K$.
--
--   This is the elementary identity measuring how far a theta factor, formed from the cross-ratio of two base points against an orbit pair $g\cdot a, g\cdot b$, deviates from $1$: the deviation is proportional to $\det g$ divided by the two linear forms $\Phi,\Phi_0$. It is used in the convergence estimates for theta products on Drinfeld's upper half plane, being cited by [`CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : GL (Fin 2) K₀) {a b : K} (z z₀ : K)
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hΦ : (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) ≠ 0)
    (hΦ₀ : (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1))) ≠ 0) :
    crossRatio z z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) a) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) b) - 1 =
      (z - z₀) * (a - b) * algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) /
        ((z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) *
          (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1)))) := by sorry
