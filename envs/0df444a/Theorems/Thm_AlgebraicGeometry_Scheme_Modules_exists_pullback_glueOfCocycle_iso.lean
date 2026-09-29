-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso
-- name    : AlgebraicGeometry.Scheme.Modules.exists_pullback_glueOfCocycle_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4a0a9773-07de-556c-9b2e-e03396625537
-- title:
--   Pullback of a glued module is the glue of the pulled-back cocycle
-- statement:
--   Let $X$ and $X'$ be schemes, let $g\colon X'\to X$ be a morphism of schemes, let $\iota$ be an index type, and let $U\colon\iota\to X.\mathrm{Opens}$ be a family of open subsets of $X$ with $\bigsqcup_i U_i=\top$. Let $c$ be a unit cocycle for $U$ in the sense of the structure `Scheme.Modules.UnitCocycle`: sections $u_{ij}\in\Gamma(X,U_i\sqcap U_j)$ with $u_{ii}=1$ and, on $U_i\sqcap U_j\sqcap U_k$, the relation $u_{ij}\,u_{jk}=u_{ik}$ after restriction. Write $\mathrm{glueOfCocycle}\,c$ for the associated sheaf of modules on $X$, whose sections over an open $T$ are the families $(x_i)_{i}$ with $x_i\in\Gamma(X,T\sqcap U_i)$ satisfying $x_i|_{T\sqcap U_i\sqcap U_j}=u_{ij}\cdot x_j|_{T\sqcap U_i\sqcap U_j}$, and $\mathrm{glueFrame}\,c\,i\in\Gamma(\mathrm{glueOfCocycle}\,c,U_i)$ for the section given by the family $k\mapsto u_{ki}$ transported along $U_i\sqcap U_k=U_k\sqcap U_i$. Let $c.\mathrm{comap}\,g$ be the unit cocycle on the preimages $g^{-1}U_i$ in $X'$ with entries $(g.\mathrm{app}(U_i\sqcap U_j))(u_{ij})$. The assertion is that there exists an isomorphism $\varphi$ of modules on $X'$ from $(\mathrm{pullback}\,g)(\mathrm{glueOfCocycle}\,c)$ to $\mathrm{glueOfCocycle}(c.\mathrm{comap}\,g)$ such that for every $i$ the component of $\varphi.\mathrm{hom}$ over $g^{-1}U_i$ carries $\mathrm{pullbackLocalSection}\,g\,(\mathrm{glueFrame}\,c\,i)$ — the image of the frame under the unit of the pullback–pushforward adjunction — to $\mathrm{glueFrame}(c.\mathrm{comap}\,g)\,i$. Only existence of such a $\varphi$ is asserted, not canonicity.
--
--   This is the compatibility of the cocycle description of a line bundle, or more generally of a module glued from trivialisations with unit transition functions, with pullback along a morphism of schemes: the pullback of the glued module is glued from the pulled-back transition functions, by an isomorphism matching the distinguished frames. It is used in the constructions producing invertible modules on a base change, for instance in the statements about pullbacks of invertible modules along separated morphisms and along direct limits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_pullback_glueOfCocycle_iso
    {X X' : Scheme.{u}} (g : X' ⟶ X) {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (c : Scheme.Modules.UnitCocycle U) :
    ∃ φ : (Scheme.Modules.pullback g).obj (Scheme.Modules.glueOfCocycle c) ≅ Scheme.Modules.glueOfCocycle (c.comap g),
      ∀ i, φ.hom.app (g ⁻¹ᵁ U i) (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.glueFrame c i)) =
        Scheme.Modules.glueFrame (c.comap g) i := by sorry
