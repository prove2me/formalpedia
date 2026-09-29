-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso_trans_tensorPowMapIso_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/5bcb88b9-e22b-5a6d-8334-f397fcdc78ac
-- title:
--   Compatibility of pullback tensor-power isomorphisms with composition
-- statement:
--   Let $c : X' \to X$ and $d : X'' \to X'$ be morphisms of schemes, let $L$, $L'$, $L''$ be objects of the categories of modules on $X$, $X'$, $X''$ respectively, and let $e : c^{*}L \cong L'$ and $e' : d^{*}L' \cong L''$ be isomorphisms, where $c^{*}$, $d^{*}$ denote the functors `Scheme.Modules.pullback`. For every $n \in \mathbb{N}$, with tensor powers taken in the recursive sense $L^{\otimes 0} = \mathbf{1}$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, the two following isomorphisms $(d \gg c)^{*}(L^{\otimes n}) \cong (L'')^{\otimes n}$ agree, where $d \gg c$ is $d$ followed by $c$. The first is the canonical isomorphism `pullbackTensorPowIso` $(d \gg c)^{*}(L^{\otimes n}) \cong ((d \gg c)^{*}L)^{\otimes n}$ (defined by the unit comparison `pullbackTensorUnitObjIso` at $n = 0$ and, inductively, by the monoidal comparison `pullbackTensorObjIso` followed by right whiskering), followed by the $n$-th tensor power `tensorPowMapIso` of the isomorphism $(d \gg c)^{*}L \cong L''$ obtained as the inverse of the component at $L$ of the comparison isomorphism `pullbackComp d c` between $d^{*}c^{*}$ and $(d \gg c)^{*}$, then $d^{*}e$, then $e'$. The second is the inverse of the component of `pullbackComp d c` at $L^{\otimes n}$, followed by $d^{*}$ applied to the corresponding isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong (L')^{\otimes n}$ for $c$ and $e$, followed by the corresponding isomorphism $d^{*}((L')^{\otimes n}) \cong (d^{*}L')^{\otimes n} \cong (L'')^{\otimes n}$ for $d$ and $e'$.
--
--   This is the cocycle, or functoriality, compatibility of the canonical identifications of inverse images of tensor powers: the trivialisation of $(d \gg c)^{*}(L^{\otimes n})$ obtained in one step agrees with the one obtained by pulling back along $c$ and then along $d$. It is the coherence input for transporting tensor-power data along composed morphisms, and is used by [`AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_comp`](thm.html#AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso_trans_tensorPowMapIso_comp
    {X X' X'' : Scheme.{u}} (c : X' ⟶ X) (d : X'' ⟶ X')
    (L : X.Modules) (L' : X'.Modules) (L'' : X''.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L') (e' : (Scheme.Modules.pullback d).obj L' ≅ L'') (n : ℕ) :
    Scheme.Modules.pullbackTensorPowIso (d ≫ c) L n ≪≫
        Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e') n
      = ((Scheme.Modules.pullbackComp d c).app (L.tensorPow n)).symm ≪≫
          (Scheme.Modules.pullback d).mapIso (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n) ≪≫
          (Scheme.Modules.pullbackTensorPowIso d L' n ≪≫ Scheme.Modules.tensorPowMapIso e' n) := by sorry
