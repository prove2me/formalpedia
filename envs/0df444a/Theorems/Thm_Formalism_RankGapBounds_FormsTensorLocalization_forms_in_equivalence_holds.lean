-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_forms_in_equivalence_holds
-- name    : Formalism.RankGapBounds.FormsTensorLocalization.forms_in_equivalence_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:45.29855+00:00
-- url     : https://prove2.me/theorems/3b377ce0-2078-43fb-bf36-eeff6a5daf83
-- title:
--   Forms Tensor Localization: forms in equivalence holds
-- statement:
--   The Forms Tensor Localization construction uses the forms in equivalence holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FormsTensorLocalization.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/FormsTensorLocalization.lean#L36-L47

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

theorem Formalism.RankGapBounds.FormsTensorLocalization.forms_in_equivalence_holds : FormsInEquiv := by sorry
