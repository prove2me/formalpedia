-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_refinement_kills_etale_system_class
-- name    : AlgebraicGeometry.Scheme.exists_refinement_kills_etale_system_class
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-25T08:20:15.545821+00:00
-- url     : https://prove2.me/theorems/669a3d0b-dde6-5f1e-9641-0506252b5b90
-- title:
--   Étale cohomology vanishing for a compatible system is detected on a refinement
-- statement:
--   Let $D$ be a cofiltered diagram of affine schemes and $F$ a compatible system of abelian étale sheaves. If a class at stage $i$ maps to zero in the cohomology of the limit sheaf, some transition $j\to i$ sends the class to zero.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitBoundaryMaps

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtaleStageCohomology (transition)
universe u

theorem AlgebraicGeometry.Scheme.exists_refinement_kills_etale_system_class
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (q : ℕ) (F : System (directImages D)) (i : I) (x : (F.obj i).H q)
    (hx : stageRestriction c hc F i q x = 0) :
    ∃ (j : I) (a : j ⟶ i), transition a F q x = 0 := by sorry
