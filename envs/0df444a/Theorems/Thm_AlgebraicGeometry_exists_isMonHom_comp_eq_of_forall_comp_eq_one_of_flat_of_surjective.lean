-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
-- name    : AlgebraicGeometry.exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0ccdda1b-6f6a-5936-bb55-0ad16ea2a661
-- title:
--   Descent of homomorphisms along a faithfully flat quasi-compact isogeny
-- statement:
--   Let $S$ be a scheme and let $A$, $B$, $C$ be objects of the over category $\mathrm{Sch}/S$, each equipped with a group object structure for the cartesian monoidal structure (fibre product over $S$). Let $f\colon A \to B$ and $g\colon A \to C$ be morphisms in $\mathrm{Sch}/S$ which are homomorphisms of monoid objects, i.e. compatible with the unit and multiplication maps. Assume that the underlying morphism of schemes $f.\mathrm{left}\colon A.\mathrm{left} \to B.\mathrm{left}$ is flat, surjective and quasi-compact. Assume further that the kernel of $f$ is contained in the kernel of $g$ in the sense of points: for every object $T$ of $\mathrm{Sch}/S$ and every $T$-point $a\colon T \to A$ such that $a$ followed by $f$ equals the neutral element of the group $\operatorname{Hom}_{\mathrm{Sch}/S}(T,B)$, the composite of $a$ with $g$ equals the neutral element of $\operatorname{Hom}_{\mathrm{Sch}/S}(T,C)$. The conclusion asserts the existence of a morphism $h\colon B \to C$ in $\mathrm{Sch}/S$ which is a homomorphism of monoid objects, satisfies $h \circ f = g$, and is the unique morphism $B \to C$ in $\mathrm{Sch}/S$ with that factorisation property (uniqueness being asserted among all $S$-morphisms, not only among homomorphisms).
--
--   This is the universal property of the quotient of a group scheme by the kernel of a faithfully flat quasi-compact homomorphism: such an $f$ is the fpqc cokernel of $\ker f$, so any homomorphism killing $\ker f$ factors uniquely through $f$. It is used in the treatment of the relative group law on good-reduction Jacobians and for the fake elliptic curves of the Čerednik–Drinfel'd setting, where factorisation of maps through isogenies is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

theorem AlgebraicGeometry.exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
    {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
    (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    ∃ h : B ⟶ C, IsMonHom h ∧ f ≫ h = g ∧ ∀ h' : B ⟶ C, f ≫ h' = g → h' = h := by sorry
