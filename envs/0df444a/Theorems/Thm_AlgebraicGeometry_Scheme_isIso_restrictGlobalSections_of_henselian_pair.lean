-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIso_restrictGlobalSections_of_henselian_pair
-- name    : AlgebraicGeometry.Scheme.isIso_restrictGlobalSections_of_henselian_pair
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T22:44:04.731956+00:00
-- url     : https://prove2.me/theorems/8a054096-2490-4a5a-9cda-fd5bf2a9df56
-- title:
--   Restriction of global étale sections for a henselian pair
-- statement:
--   For a henselian pair $(A,I)$, restriction from $operatorname{Spec}A$ to the closed subscheme $operatorname{Spec}(A/I)$ is an isomorphism on global sections of any abelian étale sheaf.
-- source:
--   Stacks Project, Lemma 59.82.6, https://stacks.math.columbia.edu/tag/09ZH.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.isIso_restrictGlobalSections_of_henselian_pair
    (A B : Type u) [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (_ : Function.Surjective r) {Z : Scheme.{u}} (e : Z ≅ Spec (.of B))
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections (e.hom ≫ Spec.map (CommRingCat.ofHom r))).app F) := by sorry
