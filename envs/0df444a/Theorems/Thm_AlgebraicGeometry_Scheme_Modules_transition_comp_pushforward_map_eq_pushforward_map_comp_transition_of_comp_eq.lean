-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
-- name    : AlgebraicGeometry.Scheme.Modules.transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a599573b-dfcf-53be-ad4c-749ac0b16ab3
-- title:
--   Naturality of the restriction transition morphism ι'_*ι'^*→ι_*ι^*
-- statement:
--   Let $Z$, $Z'$, $X$ be schemes and let $t \colon Z \to Z'$, $\iota' \colon Z' \to X$, $\iota \colon Z \to X$ be morphisms with $\iota' \circ t = \iota$, witnessed by $h$. Let $N, N'$ be $\mathcal{O}_X$-modules, let $\varphi' \colon \iota'^*N \to \iota'^*N'$ be a morphism of $\mathcal{O}_{Z'}$-modules, and let $\varphi \colon \iota^*N \to \iota^*N'$ be a morphism of $\mathcal{O}_Z$-modules which is assumed to be obtained from $t^*\varphi'$ by conjugation with the canonical isomorphisms $t^*\iota'^* \cong (\iota' \circ t)^* \cong \iota^*$, namely the composite of `Scheme.Modules.pullbackComp t ι'` and `Scheme.Modules.pullbackCongr h` at $N$ and at $N'$: explicitly, $\varphi$ is the inverse of that isomorphism at $N$, followed by $t^*\varphi'$, followed by that isomorphism at $N'$. For an $\mathcal{O}_X$-module $M$ write $T_M \colon \iota'_*\iota'^*M \to \iota_*\iota^*M$ for the composite of $\iota'_*$ applied to the unit of the adjunction $t^* \dashv t_*$ at $\iota'^*M$, then the component of `Scheme.Modules.pushforwardComp t ι'` at $t^*\iota'^*M$, then $(\iota' \circ t)_*$ applied to the two pullback identifications above, then the component of `Scheme.Modules.pushforwardCongr h` at $\iota^*M$. The conclusion is that $T_N$ followed by $\iota_*\varphi$ equals $\iota'_*\varphi'$ followed by $T_{N'}$.
--
--   This is the naturality, in compatible morphisms of restricted modules, of the transition morphism comparing $\iota'_*\iota'^*$ with $\iota_*\iota^*$ along a commuting triangle of scheme morphisms. It is used in the construction of isomorphisms of invertible modules from compatible systems of isomorphisms over adic thickenings, where the triangles are those of successive thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
    {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι) (N N' : X.Modules)
    (φ' : (Scheme.Modules.pullback ι').obj N ⟶ (Scheme.Modules.pullback ι').obj N')
    (φ : (Scheme.Modules.pullback ι).obj N ⟶ (Scheme.Modules.pullback ι).obj N')
    (hφ : φ =
      ((Scheme.Modules.pullbackComp t ι').app N ≪≫ (Scheme.Modules.pullbackCongr h).app N).inv
        ≫ (Scheme.Modules.pullback t).map φ'
        ≫ ((Scheme.Modules.pullbackComp t ι').app N' ≪≫ (Scheme.Modules.pullbackCongr h).app N').hom) :
    ((Scheme.Modules.pushforward ι').map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N))
      ≫ (Scheme.Modules.pushforward ι).map φ =
    (Scheme.Modules.pushforward ι').map φ'
      ≫ ((Scheme.Modules.pushforward ι').map
          ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N'))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N'))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N')
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N')
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N')) := by sorry
