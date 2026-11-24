-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_appLE_mem_comap_ideal
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.appLE_mem_comap_ideal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:16.34132+00:00
-- url     : https://prove2.me/theorems/b5e54fa1-b54d-462a-bd38-567c99cd3112
-- title:
--   Ideal Sheaf Data: app LE mem comap ideal
-- statement:
--   The Ideal Sheaf Data construction uses the app LE mem comap ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L194-L199

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.appLE_mem_comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) {x : Γ(Y, (U : Y.Opens))}
    (hx : x ∈ I.ideal U) :
    (f.appLE (U : Y.Opens) (V : X.Opens) e).hom x ∈ (I.comap f).ideal V := by sorry
