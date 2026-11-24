-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_mapDomain
-- name    : Formalism.GM.leadingTermLemmas.wf_mapDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:48.279104+00:00
-- url     : https://prove2.me/theorems/430c7f27-5ab5-48a2-8e8e-60f1cb6811e9
-- title:
--   leading Term Lemmas: wf map Domain
-- statement:
--   The leading Term Lemmas construction uses the wf map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1138-L1149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1138-L1149

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.wf_mapDomain (m : Fin (N + 1) × Fin r →₀ ℕ) :
    (wf (m.mapDomain (cs' (N := N))) : K) = wf m := by sorry
