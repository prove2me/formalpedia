-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_span_image
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:03.056978+00:00
-- url     : https://prove2.me/theorems/bc3b7564-ecdb-4a2e-b057-02316952bfd7
-- title:
--   Ideal Sheaf Data: comap ideal eq span image
-- statement:
--   The Ideal Sheaf Data construction uses the comap ideal eq span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L201-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L201-L207

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) (s : Set Γ(Y, (U : Y.Opens)))
    (hs : I.ideal U = Ideal.span s) :
    (I.comap f).ideal V
      = Ideal.span ((f.appLE (U : Y.Opens) (V : X.Opens) e).hom '' s) := by sorry
