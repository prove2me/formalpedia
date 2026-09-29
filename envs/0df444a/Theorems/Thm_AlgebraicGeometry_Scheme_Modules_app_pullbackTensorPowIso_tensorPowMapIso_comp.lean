-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_comp
-- name    : AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/555da323-9cb6-56da-842e-672a2020a452
-- title:
--   Tensor-power pull-back comparison of sections is compositional
-- statement:
--   Let $c : X' \to X$ and $d : X'' \to X'$ be morphisms of schemes, and let $L$, $L'$, $L''$ be modules on $X$, $X'$, $X''$ respectively, together with isomorphisms $e : c^{*}L \cong L'$ and $e' : d^{*}L' \cong L''$ (pull-back being the functor `Scheme.Modules.pullback`). Fix $n \in \mathbb{N}$ and a global section $s$ of the $n$-th tensor power `L.tensorPow n`, formed recursively as the monoidal unit for $n = 0$ and as `L.tensorPow n ⊗ L` at each step. For each morphism, `pullbackTensorPowIso` is the isomorphism $f^{*}(M^{\otimes n}) \cong (f^{*}M)^{\otimes n}$ built recursively from the inverse monoidal unit and tensor-product comparisons of the pull-back functor, and `tensorPowMapIso` is the $n$-fold tensor power of an isomorphism of modules. The assertion is an equality of global sections of $L''^{\otimes n}$ on $\top$: applying, to the image of $s$ under the unit of the adjunction `pullbackPushforwardAdjunction (d ≫ c)` at `L.tensorPow n`, the isomorphism `pullbackTensorPowIso (d ≫ c) L n` followed by the $n$-th tensor power of the composite $((d\circ c)^{*}L \cong d^{*}c^{*}L) \ggg d^{*}e \ggg e'$, gives the same result as first applying the unit for $c$ and the isomorphism `pullbackTensorPowIso c L n` followed by the $n$-th power of $e$, then the unit for $d$, then `pullbackTensorPowIso d L' n` followed by the $n$-th power of $e'$.
--
--   This is the compatibility, with composition of morphisms of schemes, of the canonical comparison maps $\Gamma(f^{*}(L^{\otimes n})) \to \Gamma((f^{*}L)^{\otimes n}) \to \Gamma(L'^{\otimes n})$ applied to pulled-back sections. It is used in [`AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback`](thm.html#AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback) to show that the induced comparison maps between the associated graded section rings compose.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_comp.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_comp
    {X X' X'' : Scheme.{u}} (c : X' ⟶ X) (d : X'' ⟶ X')
    (L : X.Modules) (L' : X'.Modules) (L'' : X''.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L') (e' : (Scheme.Modules.pullback d).obj L' ≅ L'')
    (n : ℕ) (s : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso (d ≫ c) L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e') n).hom.app ⊤)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (d ≫ c)).unit.app (L.tensorPow n)).app ⊤) s)
      = ((Scheme.Modules.pullbackTensorPowIso d L' n ≪≫ Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app (L'.tensorPow n)).app ⊤)
            (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
              ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) s))) := by sorry
