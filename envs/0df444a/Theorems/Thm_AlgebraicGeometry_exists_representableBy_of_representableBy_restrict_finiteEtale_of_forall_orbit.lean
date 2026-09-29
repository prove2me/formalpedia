-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
-- name    : AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a7dd114f-2e9c-5b69-b54e-59653184fecc
-- title:
--   Finite étale descent of a representing scheme, orbit form
-- statement:
--   Let $R$ be a commutative ring and $R'$ a commutative $R$-algebra which is finite, étale and faithfully flat over $R$, and write $s = \operatorname{Spec}(R \to R')$ for the induced morphism $\operatorname{Spec} R' \to \operatorname{Spec} R$. Let $G$ be a presheaf on the category of schemes over $\operatorname{Spec} R$ (a functor $(\mathrm{Over}\,(\operatorname{Spec} R))^{\mathrm{op}} \to \mathrm{Type}\,(u+1)$) such that for every object $T$ over $\operatorname{Spec} R$, $G$ satisfies the sheaf condition for the one-morphism presieve consisting of the counit $\mathrm{Over}.\mathrm{map}\,s\,(\mathrm{Over}.\mathrm{pullback}\,s\,T) \to T$ of the adjunction `Over.mapPullbackAdj` at $T$, i.e. for the base-change morphism $T \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to T$. Let $x' : X' \to \operatorname{Spec} R'$ be a scheme over $\operatorname{Spec} R'$ and suppose the restricted presheaf $(\mathrm{Over}.\mathrm{map}\,s)^{\mathrm{op}} \ggg G$ on schemes over $\operatorname{Spec} R'$ is represented by $\mathrm{Over}.\mathrm{mk}\,x'$. Let $a =$ `DescentAction.ofRepresentableBy` be the descent action on $x'$ read off from this representation: a morphism $a : X' \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to X'$ (the pullback of $x' \ggg s$ along $s$) over the second projection, unital along `DescentAction.unitMap` and transitive in the sense of the two composites of `DescentAction.actMap` and the $(1,3)$-projection. Assume finally that each orbit lies in an affine chart: for every point $x$ of $X'$ there is an affine open $U \subseteq X'$ with $a(r) \in U$ for every point $r$ of that pullback whose first projection is $x$. Then there exist a scheme $X$, a morphism $f : X \to \operatorname{Spec} R$, a representation of $G$ by $\mathrm{Over}.\mathrm{mk}\,f$, and an isomorphism $e : X \times_{\operatorname{Spec} R} \operatorname{Spec} R' \xrightarrow{\sim} X'$ with $e$ followed by $x'$ equal to the second projection.
--
--   This is the descent statement that converts representability of a functor after a finite étale faithfully flat base change $R \to R'$ into representability over $R$, in the form whose affineness hypothesis is about orbits of the descent action through a single point rather than about arbitrary finite subsets of a fibre. It is used in the construction of a scheme representing a relative Picard-type subfunctor, via [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G (Presieve.singleton
      ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R R')))).counit.app T)))
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hX' : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R R')))).op ⋙ G).RepresentableBy (Over.mk x'))
    (haff : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) r = x →
        (DescentAction.ofRepresentableBy (Spec.map (CommRingCat.ofHom (algebraMap R R'))) G x' hX').act r ∈ U) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (_ : G.RepresentableBy (Over.mk f))
      (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X'),
      e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by sorry
