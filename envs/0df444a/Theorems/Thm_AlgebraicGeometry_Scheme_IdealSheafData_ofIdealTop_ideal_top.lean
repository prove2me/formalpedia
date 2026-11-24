-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:37.263818+00:00
-- url     : https://prove2.me/theorems/ba19a91a-ad36-4cbb-b009-15d70cc7130b
-- title:
--   Ideal Sheaf Data: of Ideal Top ideal top
-- statement:
--   The Ideal Sheaf Data construction uses the of Ideal Top ideal top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L68-L72

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top {Z : Scheme.{u}} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by sorry
