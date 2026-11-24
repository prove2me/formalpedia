-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_Kab_smul
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_Kab_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:07.90681+00:00
-- url     : https://prove2.me/theorems/6a8621d4-ba9a-4404-93bb-b25de691adca
-- title:
--   Levi Coordinates: rrka Kab smul
-- statement:
--   The Levi Coordinates construction uses the rrka Kab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L30-L36

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

theorem Formalism.MainNotions.LeviCoordinates.rrka_Kab_smul (δ : Γ) (x y : G) : rrk_Kab Γ φ ((δ : G) * y) x = rrk_Kab Γ φ y x := by sorry
