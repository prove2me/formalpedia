-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_zpow_iso_tensorPow_of_symmetric
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/3e23cf65-17e9-56b4-b863-b7bd7fa93822
-- title:
--   Mumford's formula for symmetric line bundles: [n]^*L≅ L^{⊗ n^2}
-- statement:
--   Let $k$ be an algebraically closed field and let $t \colon X \to \operatorname{Spec} k$ be a morphism of schemes, where the object `Over.mk t` of the category of $k$-schemes is equipped with the structure of a group object which is moreover a commutative monoid object; assume $t$ is smooth, proper and geometrically connected. Let $L$ be an $\mathcal{O}_X$-module (an object of `X.Modules`) which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of $U$. The group structure on the hom-set makes the identity $\mathbb 1$ of `Over.mk t` an element of a group, so that $\mathbb 1^{\,n}$ for $n \in \mathbb Z$ has underlying morphism $[n] \colon X \to X$ and $\mathbb 1^{-1}$ has underlying morphism the inversion $[-1]$. Assume $L$ is symmetric, i.e. the type of isomorphisms between the pullback of $L$ along $[-1]$ and $L$ is nonempty. Then for every integer $n$ there is an isomorphism between the pullback of $L$ along $[n]$ and the iterated tensor power $L^{\otimes m}$, where $m = (n\cdot n).\mathrm{toNat} = n^2$ and the tensor power is defined recursively by $L^{\otimes 0} = \mathbf 1$ and $L^{\otimes (j+1)} = L^{\otimes j} \otimes L$; the conclusion asserts nonemptiness of the type of such isomorphisms, not a chosen one.
--
--   This is the symmetric case of Mumford's formula for an abelian variety over an algebraically closed field, obtained from the theorem of the cube; it is used here in the form $[n]^*L \cong L^{\otimes n^2}$. It feeds the computation of the degree of the endomorphism $n \cdot \mathrm{id}$ of a relative group law in the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_zpow_iso_tensorPow_of_symmetric
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t))⁻¹).left).obj L ≅ L)) (n : ℤ) :
    Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t)) ^ n).left).obj L ≅ L.tensorPow (n * n).toNat) := by sorry
