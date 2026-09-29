-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/cace9770-33e7-524a-afb0-e11f022757b2
-- title:
--   Zero-scheme ideals agreeing in codimension ≤ 1 coincide
-- statement:
--   Let $X$ be a scheme which is integral and locally Noetherian, and assume that for every point $x$ of $X$ the local ring $\mathcal O_{X,x}$ is a domain and is integrally closed in its fraction field. Let $M$ and $M'$ be $\mathcal O_X$-modules (objects of `X.Modules`) which satisfy `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ on which the pullback of the module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules of $U$. Let $s : \mathbf 1 \to M$ and $s' : \mathbf 1 \to M'$ be morphisms from the monoidal unit, that is global sections, with $s \neq 0$. For a section $t$, `Scheme.Modules.zeroSchemeIdeal t` denotes the infimum, as ideal sheaf data on $X$, of all ideal sheaf data $J$ with $\mathrm{coeffIdeal}(t, U) \le J(U)$ for every affine open $U$, where $\mathrm{coeffIdeal}(t,U)$ is the ideal of $\Gamma(X,U)$ spanned by the range of the coefficient map of $t$ over $U$. The hypothesis is that for every $x \in X$ with $\operatorname{ringKrullDim} \mathcal O_{X,x} \le 1$, and every affine open $U$ containing $x$, the images of the ideals $(\mathrm{zeroSchemeIdeal}\,s)(U)$ and $(\mathrm{zeroSchemeIdeal}\,s')(U)$ under the germ map $\Gamma(X,U) \to \mathcal O_{X,x}$ agree. The conclusion is the equality $\mathrm{zeroSchemeIdeal}\,s = \mathrm{zeroSchemeIdeal}\,s'$ of ideal sheaf data on $X$.
--
--   This is the scheme-theoretic form of the statement that on a normal locally Noetherian integral scheme the zero scheme of a nonzero section of a line bundle is determined by its behaviour at points of codimension at most one, i.e. the injectivity of the map from Cartier to Weil divisors combined with algebraic Hartogs' principle. It is used in the construction of the relative Picard functor and of Néron models, via the comparison of zero-scheme ideals under a morphism of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M') (hs : s ≠ 0)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → ∀ (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ U x hxU).hom ((Scheme.Modules.zeroSchemeIdeal s).ideal U) =
        Ideal.map (X.presheaf.germ U x hxU).hom ((Scheme.Modules.zeroSchemeIdeal s').ideal U)) :
    Scheme.Modules.zeroSchemeIdeal s = Scheme.Modules.zeroSchemeIdeal s' := by sorry
