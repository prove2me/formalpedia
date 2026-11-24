-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictGlobalSections_of_separably_closed_field_extension
-- name    : AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T01:12:31.846667+00:00
-- url     : https://prove2.me/theorems/defc92f6-ca4a-49fc-897d-c776cf19d8b4
-- title:
--   Étale global sections are invariant under extension of a separably closed field
-- statement:
--   Let $Z$ be proper over a separably closed field $L$, and let $E$ be an algebraically closed extension of $L$. For any abelian étale sheaf $F$ on $Z$, the canonical restriction on global sections to $Z_E$ is an isomorphism.
-- source:
--   Stacks Project, Lemma 59.39.5, https://stacks.math.columbia.edu/tag/0A3I.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
universe u

theorem AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension
    (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsAlgClosed E]
    (g : L →+* E) {Z B : Scheme.{u}} (p : Z ⟶ Spec (.of L)) [IsProper p]
    (j : B ⟶ Spec (.of E)) (a : B ⟶ Z) (_h : IsPullback j a (Spec.map (CommRingCat.ofHom g)) p)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections a).app F) := by sorry
