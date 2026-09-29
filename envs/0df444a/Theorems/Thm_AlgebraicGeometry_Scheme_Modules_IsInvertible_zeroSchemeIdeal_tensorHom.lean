-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/49821138-ef40-53a0-8683-52290b290d99
-- title:
--   Additivity of zero-scheme ideals under tensor product of sections
-- statement:
--   Let $X$ be a scheme and let $L$ and $M$ be objects of the monoidal category `X.Modules` of sheaves of modules on $X$. Assume $L$ and $M$ are invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of the module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$. Let $s \colon \mathbb{1} \to L$ and $s' \colon \mathbb{1} \to M$ be morphisms from the monoidal unit, i.e. global sections of $L$ and of $M$. From these a global section of $L \otimes M$ is formed as the inverse of the left unitor $\mathbb{1} \to \mathbb{1} \otimes \mathbb{1}$ followed by $s \otimes s'$. The assertion is an identity of ideal sheaf data on $X$: the ideal sheaf $\mathrm{zeroSchemeIdeal}$ of this section of $L \otimes M$ equals the product, in the semiring of ideal sheaf data $X.\mathrm{IdealSheafData}$, of the ideal sheaves $\mathrm{zeroSchemeIdeal}$ of $s$ and of $s'$. Here $\mathrm{zeroSchemeIdeal}$ of a global section $t$ of a module is defined as the infimum of all ideal sheaf data $J$ on $X$ with $\mathrm{coeffIdeal}\,t\,U \le J.\mathrm{ideal}\,U$ for every affine open $U$, where $\mathrm{coeffIdeal}\,t\,U$ is the ideal of $\Gamma(X,U)$ spanned by the range of the coefficient function of $t$ on $U$.
--
--   This is the additivity of the divisor of zeros of a section of a line bundle under tensor product, $\operatorname{div}(s \otimes s') = \operatorname{div}(s) + \operatorname{div}(s')$, in the form of an equality of vanishing ideal sheaves. It is used to compute the vanishing locus of a section of a tensor power, in particular in [`AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    Scheme.Modules.zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')) =
      Scheme.Modules.zeroSchemeIdeal s * Scheme.Modules.zeroSchemeIdeal s' := by sorry
