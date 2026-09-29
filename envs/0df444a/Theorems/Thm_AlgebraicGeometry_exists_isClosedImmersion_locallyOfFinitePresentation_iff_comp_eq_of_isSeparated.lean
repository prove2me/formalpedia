-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
-- name    : AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/8a6c31e7-eb7b-5324-81da-73e2a42e6d3a
-- title:
--   Equaliser of two S-points of a separated scheme
-- statement:
--   Let $H$, $S$, $T$ be schemes, let $q : H \to S$ be a separated morphism, let $t : T \to S$ be a morphism, and let $u, v : T \to H$ be two morphisms with $u$ followed by $q$ equal to $t$ and $v$ followed by $q$ equal to $t$, i.e. two $S$-morphisms $T \to H$ over $t$. The assertion is the existence of a scheme $Z$ and a morphism $j : Z \to T$ such that: (i) $j$ is a closed immersion; (ii) if $q$ is locally of finite type, then $j$ is locally of finite presentation; and (iii) $j$ represents the equaliser of $u$ and $v$ in the following sense: for every scheme $T'$ and every morphism $\psi : T' \to T$, one has $\psi$ followed by $u$ equal to $\psi$ followed by $v$ if and only if there is a morphism $\psi' : T' \to Z$ with $\psi'$ followed by $j$ equal to $\psi$. Note that (iii) asserts only the existence of a factorisation, not its uniqueness (which would in any case follow from (i)); the implication in (ii) is stated as a hypothesis on $q$ rather than as an unconditional claim.
--
--   This is the standard fact that the equaliser of two $S$-valued points of a separated $S$-scheme is a closed subscheme of the base, together with the refinement that the corresponding closed immersion is locally of finite presentation as soon as the structure morphism is locally of finite type. It is used in the construction of Hom-schemes for abelian schemes (cutting out $\mathrm{Hom}$ inside a scheme of morphisms as the locus where two maps agree) and in the proper/flat descent statement [`AlgebraicGeometry.exists_ideal_fg_forall_pullback_fst_comp_eq_iff_map_eq_bot_of_isProper_of_flat`](thm.html#AlgebraicGeometry.exists_ideal_fg_forall_pullback_fst_comp_eq_iff_map_eq_bot_of_isProper_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H) (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧ (LocallyOfFiniteType q → LocallyOfFinitePresentation j) ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by sorry
