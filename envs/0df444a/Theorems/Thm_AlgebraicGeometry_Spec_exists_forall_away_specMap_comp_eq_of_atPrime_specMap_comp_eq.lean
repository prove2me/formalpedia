-- Prove2me | Theorems.Thm_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
-- name    : AlgebraicGeometry.Spec.exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/0fe114f0-83fa-5d30-9c33-fbfd637ad245
-- title:
--   Equality of two Spec A-points spreads from 𝔭 to a basic open
-- statement:
--   Let $A$ be a Noetherian commutative ring, $\mathfrak p \subset A$ a prime ideal, and $L$ an $A$-algebra which is a localisation of $A$ at $\mathfrak p$ (i.e. a localisation at the multiplicative set $A \setminus \mathfrak p$). Let $X$ be a scheme (in the bottom universe) and let $y, y' : \operatorname{Spec} A \to X$ be two morphisms of schemes, where $\operatorname{Spec} A$ is the spectrum of $A$ viewed as an object of `CommRingCat`. Assume that $y$ and $y'$ become equal after restriction along the structure map, i.e. that the composite of $\operatorname{Spec}(A \to L)$ with $y$ equals the composite of $\operatorname{Spec}(A \to L)$ with $y'$. The conclusion is that there exists an element $f \in A$ with $f \notin \mathfrak p$ such that for *every* $A$-algebra $A_f$ which is a localisation of $A$ away from $f$, the composite of $\operatorname{Spec}(A \to A_f)$ with $y$ equals the composite of $\operatorname{Spec}(A \to A_f)$ with $y'$. Thus the agreement of the two $A$-points over the local ring at $\mathfrak p$ already takes place over a basic open neighbourhood $D(f)$ of $\mathfrak p$, uniformly in the chosen model of the localisation.
--
--   This is the uniqueness half of the standard "spreading out" principle: two morphisms from $\operatorname{Spec} A$ to a scheme that agree on the local ring at a point agree on an open neighbourhood of that point, here refined to a basic open $D(f)$. It is used in the Čerednik–Drinfeld part of the development, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_away_map_eq_of_atPrime_map_eq_of_rigidifiedToG`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_away_map_eq_of_atPrime_map_eq_of_rigidifiedToG), to descend an identity of morphisms from the local ring at a prime to a localisation away from a single element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Spec.exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
    {A : Type} [CommRing A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (L : Type) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L 𝔭]
    {X : Scheme.{0}} (y y' : Spec (CommRingCat.of A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y') :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ (Af : Type) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af],
      Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y' := by sorry
