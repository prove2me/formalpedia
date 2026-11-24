-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_prod_eq_wf
-- name    : Formalism.GM.leadingTermLemmas.prod_eq_wf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:51.352002+00:00
-- url     : https://prove2.me/theorems/7bab21ab-877a-4510-b6ad-6553f4b05255
-- title:
--   leading Term Lemmas: prod eq wf
-- statement:
--   The leading Term Lemmas construction uses the prod eq wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L13-L14

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

theorem Formalism.GM.leadingTermLemmas.prod_eq_wf (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : K)) = wf m := by sorry
