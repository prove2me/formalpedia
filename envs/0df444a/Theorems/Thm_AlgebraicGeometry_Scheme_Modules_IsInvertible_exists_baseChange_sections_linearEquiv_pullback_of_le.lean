-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/c6f06d0d-52a8-5a71-8530-464ea9799046
-- title:
--   Affine-local base change of sections of an invertible pullback
-- statement:
--   Let $p\colon Z\to X$ be a morphism of schemes and let $L$ be a sheaf of modules on $X$ which is invertible in the sense that every point $x\in X$ has an open neighbourhood $U$ for which the inverse image of $L$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module on $U$ (the structure sheaf viewed as a module over itself). Let $U\subseteq X$ be an open subscheme which is affine, and let $W\subseteq Z$ be an affine open with $W\le p^{-1}U$. Regard $\Gamma(Z,W)$ as a $\Gamma(X,U)$-algebra by means of the ring map `p.appLE U W hWU`, that is, $p^{\sharp}$ on $U$ followed by restriction to $W$. The assertion is that there exists a $\Gamma(Z,W)$-linear isomorphism
--   $$\beta\colon \Gamma(Z,W)\otimes_{\Gamma(X,U)}\Gamma(L,U)\;\xrightarrow{\ \sim\ }\;\Gamma\big((\text{Modules.pullback } p)(L),\,W\big)$$
--   such that for every section $s\in\Gamma(L,U)$ one has $\beta(1\otimes s)$ equal to the restriction along $W\le p^{-1}U$ of `Scheme.Modules.pullbackLocalSection p s`, the section of $p^{*}L$ over $p^{-1}U$ obtained by applying the component at $U$ of the unit of the pullback–pushforward adjunction for $p$ at $L$ to $s$.
--
--   This is the affine-local computation of the sections of an inverse-image invertible module: over an affine open $W$ contained in the preimage of an affine open $U$, the sections of $p^{*}L$ form the base change of $\Gamma(L,U)$ along $\Gamma(X,U)\to\Gamma(Z,W)$, with the pulled-back sections corresponding to $1\otimes s$. It refines the earlier version requiring $p^{-1}U$ itself to be affine, and is used for sections of invertible modules over affine boxes $p_1^{-1}U\cap p_2^{-1}V$ in a product, as in [`AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Opposite

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback_of_le
    {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (W : Z.Opens) (hW : IsAffineOpen W) (hWU : W ≤ p ⁻¹ᵁ U) :
    letI := (p.appLE U W hWU).hom.toAlgebra
    ∃ β : Γ(Z, W) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, W)] Γ((Scheme.Modules.pullback p).obj L, W),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) =
        ((Scheme.Modules.pullback p).obj L).presheaf.map (homOfLE hWU).op (Scheme.Modules.pullbackLocalSection p s) := by sorry
