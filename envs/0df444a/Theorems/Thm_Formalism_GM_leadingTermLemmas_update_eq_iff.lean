-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_update_eq_iff
-- name    : Formalism.GM.leadingTermLemmas.update_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:14.42306+00:00
-- url     : https://prove2.me/theorems/59192996-a325-4587-9f9c-a4342950848a
-- title:
--   leading Term Lemmas: update eq iff
-- statement:
--   The leading Term Lemmas construction uses the update eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1507-L1516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1507-L1516

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.update_eq_iff (m m' : Fin (N + 1) × Fin r →₀ ℕ) (h : m (Fin.last N, ρ) = m' (Fin.last N, ρ)) :
    Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0 ↔ m = m' := by sorry
