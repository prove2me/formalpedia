-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4107ce14-5844-5d3c-ac5a-15c43ac90456
-- title:
--   Zero scheme of a tensor product of sections: Z(s⊗ s')=Z(s)+Z(s')
-- statement:
--   Let $X$ be a scheme and let $L$, $M$ be objects of the category $X.\mathrm{Modules}$ of sheaves of modules on $X$, each assumed invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \ni x$ such that the pullback of the module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $s : \mathbf{1} \to L$ and $s' : \mathbf{1} \to M$ be morphisms from the monoidal unit, i.e. global sections of $L$ and of $M$. Form the global section of $L \otimes M$ given by the inverse of the left unitor $\mathbf{1} \otimes \mathbf{1} \cong \mathbf{1}$ followed by $s \otimes s'$. The assertion is an equality of ideal sheaf data on $X$: the ideal sheaf data `zeroSchemeIdeal` of this tensored section equals the product of the ideal sheaf data of $s$ and of $s'$. Here `zeroSchemeIdeal t` is, for a section $t$, the infimum of those ideal sheaf data $J$ on $X$ such that for every affine open $U$ of $X$ the coefficient ideal `coeffIdeal t U` — the ideal of $\Gamma(X,U)$ spanned by the range of the coefficient map `coeff t U` — is contained in the ideal $J$ assigns to $U$.
--
--   This is the additivity of the divisor of zeros of a section of a line bundle under tensor product, $\operatorname{div}(s \otimes s') = \operatorname{div}(s) + \operatorname{div}(s')$, expressed as multiplicativity of the associated ideal sheaves. It is used in the treatment of polarisations and of zero schemes of sections of tensor powers, for instance in producing frames and in computing the support of the zero scheme of a section of a threefold tensor power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    Scheme.Modules.zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')) =
      Scheme.Modules.zeroSchemeIdeal s * Scheme.Modules.zeroSchemeIdeal s' := by sorry
