-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
-- name    : AlgebraicGeometry.DescentAction.effective_of_finiteEtale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/29ff4b09-b464-5a47-adde-2f60027df26e
-- title:
--   Effectivity of descent data along a finite étale base change
-- statement:
--   Let $R \to R'$ be a ring homomorphism of commutative rings (in a fixed universe) making $R'$ a finite, étale and faithfully flat $R$-algebra, and write $s = \operatorname{Spec}(R \to R')\colon \operatorname{Spec} R' \to \operatorname{Spec} R$ for the induced morphism of affine schemes. Let $x'\colon X' \to \operatorname{Spec} R'$ be a scheme over $\operatorname{Spec} R'$, and let $A$ be a descent datum for $x'$ along $s$ in action form, that is: a morphism $\mathrm{act}\colon X' \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to X'$ from the fibre product of $x' \circ s$ with $s$, satisfying $\mathrm{act}$ followed by $x'$ equals the second projection, the unit law that the section $(\mathrm{id}_{X'}, x')$ of the fibre product followed by $\mathrm{act}$ is $\mathrm{id}_{X'}$, and the cocycle law equating, on the triple product, the morphism induced by $\mathrm{act}$ on the first factor followed by $\mathrm{act}$ with the $(1,3)$-projection followed by $\mathrm{act}$. Assume moreover that for every finite set of points of $X'$ there is an affine open subscheme of $X'$ containing all of them. Then $A$ is effective: there exist a scheme $X$, a morphism $f\colon X \to \operatorname{Spec} R$, an isomorphism $e\colon X \times_{\operatorname{Spec} R} \operatorname{Spec} R' \xrightarrow{\sim} X'$ with $e$ followed by $x'$ the second projection, and such that $e$ transports the canonical descent datum on the base change $X \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ (given by the flip of the two factors) to $\mathrm{act}$.
--
--   This is the effectivity of descent data for schemes along a finite étale (faithfully flat) base change, under the hypothesis that finite subsets of $X'$ lie in affine opens, in the tradition of SGA 1, Exp. VIII and of Bosch–Lütkebohmert–Raynaud, Néron Models 6.2. It is used to descend representability statements along a finite étale extension, and in the construction of relative group laws with open-immersion structure over henselian local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.DescentAction.effective_of_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by sorry
