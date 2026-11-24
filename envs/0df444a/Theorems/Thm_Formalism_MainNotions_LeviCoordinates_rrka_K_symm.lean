-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_K_symm
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_K_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:02.845257+00:00
-- url     : https://prove2.me/theorems/a4366212-cb3d-40a7-bd39-b03058bc0fcd
-- title:
--   Levi Coordinates: rrka K symm
-- statement:
--   The Levi Coordinates construction uses the rrka K symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L22-L28

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] {Γ : Subgroup G} {φ : G → ℂ}

theorem Formalism.MainNotions.LeviCoordinates.rrka_K_symm (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_K Γ φ y x = star (rrk_K Γ φ x y) := by sorry
