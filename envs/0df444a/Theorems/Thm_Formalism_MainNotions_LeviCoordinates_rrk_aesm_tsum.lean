-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrk_aesm_tsum
-- name    : Formalism.MainNotions.LeviCoordinates.rrk_aesm_tsum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:04.197136+00:00
-- url     : https://prove2.me/theorems/e667e345-9851-4331-821d-e0d519f98b1a
-- title:
--   Levi Coordinates: rrk aesm tsum
-- statement:
--   The Levi Coordinates construction uses the rrk aesm tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkAesmTsum.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkAesmTsum.lean#L16-L23

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
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
variable {G : Type*} [Group G]

theorem Formalism.MainNotions.LeviCoordinates.rrk_aesm_tsum {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hs : ∀ᵐ x ∂μ, Summable fun i => f i x) :
    AEStronglyMeasurable (fun x => ∑' i, f i x) μ := by sorry
