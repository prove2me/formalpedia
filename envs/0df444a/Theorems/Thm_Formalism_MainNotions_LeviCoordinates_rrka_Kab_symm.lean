-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_Kab_symm
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_Kab_symm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:57:07.035083+00:00
-- url     : https://prove2.me/theorems/5f53c8a2-bd03-4b81-985f-528ffc54ac5a
-- title:
--   Levi Coordinates: rrka Kab symm
-- statement:
--   The Levi Coordinates construction uses the rrka Kab symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L14-L20

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

theorem Formalism.MainNotions.LeviCoordinates.rrka_Kab_symm (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_Kab Γ φ y x = rrk_Kab Γ φ x y := by sorry
