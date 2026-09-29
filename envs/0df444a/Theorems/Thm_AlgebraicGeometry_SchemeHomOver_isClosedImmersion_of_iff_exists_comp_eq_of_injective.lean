-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective
-- name    : AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/df1377c9-2960-500c-a649-33ffa639d474
-- title:
--   Closed immersion from a functorial factorisation criterion
-- statement:
--   Let $k$ be an algebraically closed field and let $G$, $D$, $K$ be schemes (all in one universe). Let $g : G \to \operatorname{Spec} k$ be a structure morphism with $G$ reduced and $g$ flat, locally of finite type and separated, let $d : D \to \operatorname{Spec} k$ be arbitrary, let $f$ be a $k$-morphism over these structure morphisms, i.e. a morphism $f.1 : G \to D$ with $f.1$ followed by $d$ equal to $g$, and let $j : K \to D$ be a closed immersion. Assume two hypotheses. First, for every scheme $T$, every $t : T \to \operatorname{Spec} k$ and every morphism $a.1 : T \to D$ with $a.1$ followed by $d$ equal to $t$: $a.1$ factors as some $b : T \to K$ followed by $j$ if and only if there is $y : T \to G$ with $y$ followed by $g$ equal to $t$ and $y$ followed by $f.1$ equal to $a.1$. Second, any two morphisms $\operatorname{Spec} k \to G$ that are sections of $g$ (each composing with $g$ to the identity) and have the same composite with $f.1$ coincide. The conclusion is that $f.1$ is a closed immersion.
--
--   This is a representability-style criterion: a $k$-morphism whose functor of points coincides with that of a closed subscheme of the target, and which is injective on $k$-points, is itself a closed immersion. It is used to identify the torus of node units as a closed subgroup scheme inside the relative Picard scheme of a curve obtained by gluing two smooth curves, in [`AlgebraicGeometry.RelPicard.exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves) and [`AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
    {k : Type u} [Field k] [IsAlgClosed k] {G D K : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [IsReduced G] [LocallyOfFiniteType g] [Flat g] [IsSeparated g]
    (d : D ⟶ Spec (CommRingCat.of k)) (f : SchemeHomOver g d) (j : K ⟶ D) [IsClosedImmersion j]
    (hpts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t d),
      (∃ b : T ⟶ K, b ≫ j = a.1) ↔ ∃ y : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp y f = a)
    (hinj : ∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      NeronModelInfra.schemeHomOverComp y f = NeronModelInfra.schemeHomOverComp y' f → y = y') :
    IsClosedImmersion f.1 := by sorry
