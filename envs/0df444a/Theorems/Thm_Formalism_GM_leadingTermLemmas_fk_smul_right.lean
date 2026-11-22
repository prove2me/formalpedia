-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_smul_right
-- name    : Formalism.GM.leadingTermLemmas.fk_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:10.707882+00:00
-- url     : https://prove2.me/theorems/08001157-0cba-47f8-a4ee-2500f1936276
-- title:
--   leading Term Lemmas: fk smul right
-- statement:
--   The leading Term Lemmas construction uses the fk smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L79-L80

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

theorem Formalism.GM.leadingTermLemmas.fk_smul_right (c : K) (F G : MvPolynomial σ K) : fk F (c • G) = c * fk F G := by sorry
