-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_isIso
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:48.278081+00:00
-- url     : https://prove2.me/theorems/5e92161f-bee1-42f9-8e8c-26266914fc12
-- title:
--   Ideal Sheaf Data: exists iso subscheme comap of is Iso
-- statement:
--   The Ideal Sheaf Data construction uses the exists iso subscheme comap of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L520-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L520-L538

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso {Y Y' : Scheme.{u}} (g : Y ⟶ Y') [IsIso g]
    (I : Y'.IdealSheafData) :
    ∃ m : (I.comap g).subscheme ⟶ I.subscheme,
      IsIso m ∧ m ≫ I.subschemeι = (I.comap g).subschemeι ≫ g := by sorry
