-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_single_add
-- name    : Formalism.GM.leadingTermLemmas.wf_single_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:46.120606+00:00
-- url     : https://prove2.me/theorems/11cea789-e887-48c5-90e7-247653b4df50
-- title:
--   leading Term Lemmas: wf single add
-- statement:
--   The leading Term Lemmas construction uses the wf single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1023-L1037
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1023-L1037

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
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.leadingTermLemmas.wf_single_add (M : σ →₀ ℕ) (i : σ) (k : ℕ) :
    (wf (Finsupp.single i k + M) : K) = (((M i + k).descFactorial k : ℕ) : K) * wf M := by sorry
