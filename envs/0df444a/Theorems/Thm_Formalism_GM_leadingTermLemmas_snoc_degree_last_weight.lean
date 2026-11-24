-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_snoc_degree_last_weight
-- name    : Formalism.GM.leadingTermLemmas.snoc_degree_last_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:09.434976+00:00
-- url     : https://prove2.me/theorems/cfc6caa0-c9f8-4d3f-9fd7-69b644e2a223
-- title:
--   leading Term Lemmas: snoc degree last weight
-- statement:
--   The leading Term Lemmas construction uses the snoc degree last weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1300-L1301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1300-L1301

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)

theorem Formalism.GM.leadingTermLemmas.snoc_degree_last_weight (n : ℕ) : (LL.snoc n).deg (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) := by sorry
