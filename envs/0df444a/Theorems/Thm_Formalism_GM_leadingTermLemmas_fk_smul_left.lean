-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_smul_left
-- name    : Formalism.GM.leadingTermLemmas.fk_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:57.300471+00:00
-- url     : https://prove2.me/theorems/95f78d73-652a-4278-8c91-536c748667d1
-- title:
--   leading Term Lemmas: fk smul left
-- statement:
--   The leading Term Lemmas construction uses the fk smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L57-L59

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

theorem Formalism.GM.leadingTermLemmas.fk_smul_left (c : K) (F G : MvPolynomial σ K) : fk (c • F) G = c * fk F G := by sorry
