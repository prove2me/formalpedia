-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_pullback_iso_tensorPow
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_normModule_pullback_iso_tensorPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/6a296659-2aeb-5e54-90e0-8b75e7883bf1
-- title:
--   Norm of a pulled-back invertible module is its d-th tensor power
-- statement:
--   Let $\pi\colon X \to Y$ be a morphism of schemes which is finite, flat and locally of finite presentation, and let $d$ be a natural number such that $\pi.\mathrm{finrank}\,y = d$ for every point $y$ of $Y$. Let $L$ be an $\mathcal{O}_Y$-module (an object of `Y.Modules`) satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $Y$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow Y$ is isomorphic to the unit object of the monoidal category of modules on $U$. Then the type of isomorphisms
--   $$\mathrm{normModule}\,\pi\,d\,(\pi^{*}L) \;\cong\; L^{\otimes d}$$
--   is nonempty, where $\mathrm{normModule}\,\pi\,d\,(M) = \det{}_d(\pi_{*}M) \otimes \bigl(\det{}_d(\pi_{*}\mathbf{1}_{X})\bigr)^{\vee}$, the dual being the internal hom into the unit object and $\mathbf{1}_X$ the unit of `X.Modules`, and where $L^{\otimes d}$ is `Scheme.Modules.tensorPow`, defined recursively by $L^{\otimes 0} = \mathbf{1}_Y$ and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. Thus the assertion is the existence of such an isomorphism, no particular isomorphism being named.
--
--   This is the classical compatibility of the norm along a finite locally free morphism of constant rank $d$ with pullback: the norm of $\pi^{*}L$ is $L^{\otimes d}$. It feeds into [`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_normModule_pullback_pullback_iso_pullback`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_isInvertible_normModule_pullback_pullback_iso_pullback), part of the infrastructure for norms of line bundles used in the construction of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_pullback_iso_tensorPow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.nonempty_normModule_pullback_iso_tensorPow
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.normModule π d ((Scheme.Modules.pullback π).obj L) ≅ L.tensorPow d) := by sorry
