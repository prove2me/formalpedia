-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/b57484af-b606-53c9-ac13-5523a0b1bbe4
-- title:
--   Base change of 𝒪(± u) for a point in the smooth locus
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a separated morphism, and let $U \subseteq C$ be an open subscheme such that the composite of the inclusion $U \hookrightarrow C$ with $c$ is smooth of relative dimension $1$. Let $T, T'$ be schemes with structure morphisms $t : T \to \operatorname{Spec} R$ and $t' : T' \to \operatorname{Spec} R$, let $u$ consist of a morphism $u : T \to C$ together with the identity $u \circ c = t$ (in diagrammatic order $u \gg c = t$), assume the set-theoretic image of $u$ is contained in $U$, and let $\psi$ consist of a morphism $\psi : T' \to T$ together with $\psi \gg t = t'$; assume moreover $(\psi \gg u) \gg c = t'$. For such data, $\mathrm{ofPoint}$ produces the relative effective Cartier divisor of degree $1$ on $C \times_{\operatorname{Spec} R} T$ whose ideal sheaf data is the kernel of the graph morphism $T \to C \times_{\operatorname{Spec} R} T$, and correspondingly on $C \times_{\operatorname{Spec} R} T'$ for the point $\psi \gg u$; `idealModule` is the associated sheaf of modules (the ideal itself) and `lineBundle` is its dual. The conclusion asserts, as two nonemptiness statements, that pulling back along the base change $1_C \times \psi : C \times_{\operatorname{Spec} R} T' \to C \times_{\operatorname{Spec} R} T$ carries the line bundle of the divisor of $u$ to a module isomorphic to the line bundle of the divisor of $\psi \gg u$, and likewise for the ideal modules. Only existence of isomorphisms is claimed, with no canonicity or compatibility asserted.
--
--   This is the base-change compatibility $(1\times\psi)^*\mathcal O(u)\cong\mathcal O(\psi^*u)$ and $(1\times\psi)^*\mathcal O(-u)\cong\mathcal O(-\psi^*u)$ for the divisor of a section landing in the relative smooth locus of a curve over a base. It feeds the construction of rigidified line bundles attached to differences of points, and through that the description of relative Picard groups and of points on models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra RelPicard

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver t c) (hu : Set.range u.1.base ⊆ (U : Set C)) (ψ : SchemeHomOver t' t)
    (hψu : (ψ.1 ≫ u.1) ≫ c = t') :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).idealModule) := by sorry
