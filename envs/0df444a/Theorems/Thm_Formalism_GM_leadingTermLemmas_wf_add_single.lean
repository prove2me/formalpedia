-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_add_single
-- name    : Formalism.GM.leadingTermLemmas.wf_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:11.39872+00:00
-- url     : https://prove2.me/theorems/6ec0c455-031b-410d-8e08-5737f70ba77b
-- title:
--   leading Term Lemmas: wf add single
-- statement:
--   The leading Term Lemmas construction uses the wf add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L16-L26

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

theorem Formalism.GM.leadingTermLemmas.wf_add_single (m : σ →₀ ℕ) (i : σ) :
    (wf (m + Finsupp.single i 1) : K) = ((m i + 1 : ℕ) : K) * wf m := by sorry
