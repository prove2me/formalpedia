-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sub_right
-- name    : Formalism.GM.leadingTermLemmas.fk_sub_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:59.244805+00:00
-- url     : https://prove2.me/theorems/811ca6d3-1a0c-4b3b-8e35-38689c5bc688
-- title:
--   leading Term Lemmas: fk sub right
-- statement:
--   The leading Term Lemmas construction uses the fk sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L82-L83

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.leadingTermLemmas.fk_sub_right (F G G' : MvPolynomial σ K) : fk F (G - G') = fk F G - fk F G' := by sorry
