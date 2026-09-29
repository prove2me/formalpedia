-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated
-- name    : AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3ebbb0f8-95b9-500b-9ffd-58d23fdc050a
-- title:
--   Equaliser locus of two S-morphisms is closed
-- statement:
--   Let $H$, $S$, $T$ be schemes (in a fixed universe), let $q \colon H \to S$ be a separated morphism, let $t \colon T \to S$, and let $u, v \colon T \to H$ be two morphisms with $q \circ u = t$ and $q \circ v = t$, i.e. two $S$-valued points of $H$ over $t$. The assertion is that there exist a scheme $Z$ and a morphism $j \colon Z \to T$ which is a closed immersion, such that for every scheme $T'$ and every morphism $\psi \colon T' \to T$ one has $u \circ \psi = v \circ \psi$ if and only if $\psi$ factors through $j$, that is, if and only if there is a morphism $\psi' \colon T' \to Z$ with $j \circ \psi' = \psi$. The scheme $T'$ is an implicit argument of the stated equivalence. No uniqueness of the factorisation $\psi'$ is asserted (although $j$, being a closed immersion, is a monomorphism), and $Z$ is produced by an existential statement rather than as a named subscheme of $T$.
--
--   This is the standard fact that, for a separated morphism $q \colon H \to S$, the locus in $T$ where two $S$-points $u,v$ of $H$ agree is a closed subscheme of $T$, represented by the preimage of the diagonal of $q$; the stated universal property is exactly the representability of the equaliser of $u$ and $v$ by a closed immersion. It is used to exhibit loci cut out by equalities of points of a Hom scheme as closed subschemes, and is cited in the construction of level generators on polarised abelian schemes and in a rigidity argument for morphisms agreeing on adic thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H) (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by sorry
