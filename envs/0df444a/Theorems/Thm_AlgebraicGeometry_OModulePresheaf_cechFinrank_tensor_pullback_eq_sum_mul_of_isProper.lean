-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_tensor_pullback_eq_sum_mul_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d9bdee87-9c71-5c1f-b8e0-5ae2b6b9af73
-- title:
--   Künneth formula for Čech ranks on a product of proper k-schemes
-- statement:
--   Let $k$ be a field and let $\pi_X\colon X\to\operatorname{Spec} k$ and $\pi_Y\colon Y\to\operatorname{Spec} k$ be proper morphisms of schemes. Let $F$ be an $\mathcal O_X$-module and $G$ an $\mathcal O_Y$-module, each assumed invertible in the sense of `Scheme.Modules.IsInvertible`: every point of the base has an open neighbourhood $U$ on which the restriction of the module along $U\hookrightarrow X$ (resp. $Y$) is isomorphic to the unit sheaf of modules of $U$. Let $\mathfrak U$, $\mathfrak V$ and $\mathfrak W$ be ordered affine covers — a finite linearly ordered index type together with affine opens whose supremum is $\top$ — of $X$, of $Y$, and of the fibre product $X\times_{\operatorname{Spec} k}Y$ respectively, and let $n$ be a natural number. Write $p_1,p_2$ for the two projections of the fibre product, and view the fibre product over $k$ through $p_1$ followed by $\pi_X$. Then the degree-$n$ Čech rank over $k$, with respect to $\mathfrak W$, of the presheaf of sections of $p_1^*F\otimes p_2^*G$ equals $\sum_{i=0}^{n}$ of the degree-$i$ Čech rank of the sections of $F$ with respect to $\mathfrak U$ times the degree-$(n-i)$ Čech rank of the sections of $G$ with respect to $\mathfrak V$. Here the Čech rank in degree $0$ is the $k$-dimension of `H0` of the ordered cover, and in degree $i+1$ the $k$-dimension of the quotient $\ker d_{i+1}/\operatorname{im} d_i$ of the ordered Čech complex.
--
--   This is the Künneth formula for the dimensions of the Čech cohomology of an external tensor product of line bundles on a product of proper schemes over a field, stated for arbitrary finite ordered affine covers of the three schemes. It is used in the computation of Euler characteristics of such external products and in the vanishing criteria for line bundles in the kernel of the relative Picard map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_tensor_pullback_eq_sum_mul_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsProper πX] [IsProper πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G)
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) (𝔚 : (pullback πX πY).OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
        ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗ (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).cechFinrank
        𝔚 n =
      ∑ i ∈ Finset.range (n + 1),
        (OModulePresheaf.ofModules πX F).cechFinrank 𝔘 i * (OModulePresheaf.ofModules πY G).cechFinrank 𝔙 (n - i) := by sorry
