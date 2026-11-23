-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sub_left
-- name    : Formalism.GM.leadingTermLemmas.fk_sub_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:34.898697+00:00
-- url     : https://prove2.me/theorems/531d33dd-1664-4600-8e6c-4ac338f147a4
-- title:
--   leading Term Lemmas: fk sub left
-- statement:
--   The leading Term Lemmas construction uses the fk sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L66-L67

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

theorem Formalism.GM.leadingTermLemmas.fk_sub_left (F F' G : MvPolynomial σ K) : fk (F - F') G = fk F G - fk F' G := by sorry
