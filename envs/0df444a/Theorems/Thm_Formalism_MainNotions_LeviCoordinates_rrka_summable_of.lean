-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_summable_of
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_summable_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:56:50.635347+00:00
-- url     : https://prove2.me/theorems/78c43dc3-9e7d-4fb2-a926-09eb16ba1c42
-- title:
--   Levi Coordinates: rrka summable of
-- statement:
--   The Levi Coordinates construction uses the rrka summable of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L71-L72

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
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem Formalism.MainNotions.LeviCoordinates.rrka_summable_of {ι : Type*} {f : ι → ℂ} (hf : ∑' i, ‖f i‖ₑ ≠ ∞) : Summable f := by sorry
