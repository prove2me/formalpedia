-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_sum_update_eq
-- name    : Formalism.GM.leadingTermLemmas.sum_update_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:15.302931+00:00
-- url     : https://prove2.me/theorems/9e994c5a-0911-4833-a29e-336665b93a5c
-- title:
--   leading Term Lemmas: sum update eq
-- statement:
--   The leading Term Lemmas construction uses the sum update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1550-L1555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1550-L1555

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
open MvPolynomial Finset Formalism.GM Filter Topology
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.sum_update_eq (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = LL.total - m (Fin.last N, ρ) := by sorry
