-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_finset_prod
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_finset_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:32.494805+00:00
-- url     : https://prove2.me/theorems/ae2d3a8c-3ed4-4af9-8467-28f27bbb7ac5
-- title:
--   Ideal Sheaf Data: comap finset prod
-- statement:
--   The Ideal Sheaf Data construction uses the comap finset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L374-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L374-L382

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
variable {X Y : Scheme.{u}}

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_finset_prod {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (F : ι → Y.IdealSheafData) :
    (∏ i ∈ s, F i).comap f = ∏ i ∈ s, (F i).comap f := by sorry
