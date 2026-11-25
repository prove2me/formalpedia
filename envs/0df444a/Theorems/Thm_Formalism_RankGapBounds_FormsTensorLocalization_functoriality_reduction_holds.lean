-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_functoriality_reduction_holds
-- name    : Formalism.RankGapBounds.FormsTensorLocalization.functoriality_reduction_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:09.738713+00:00
-- url     : https://prove2.me/theorems/c888ab7a-fbd8-480e-840e-fb226ff0ba32
-- title:
--   Forms Tensor Localization: functoriality reduction holds
-- statement:
--   The Forms Tensor Localization construction uses the functoriality reduction holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FormsTensorLocalization.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FormsTensorLocalization.lean#L28-L34

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG

theorem Formalism.RankGapBounds.FormsTensorLocalization.functoriality_reduction_holds : FunctStep := by sorry
