-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_split
-- name    : Formalism.GM.leadingTermLemmas.wf_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:38.475476+00:00
-- url     : https://prove2.me/theorems/5057bed2-9da4-4e96-b496-ba16adcae16e
-- title:
--   leading Term Lemmas: wf split
-- statement:
--   The leading Term Lemmas construction uses the wf split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1495-L1505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1495-L1505

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

theorem Formalism.GM.leadingTermLemmas.wf_split (m : Fin (N + 1) × Fin r →₀ ℕ) :
    (wf m : K) = ((m (Fin.last N, ρ)).factorial : K) * wf (Finsupp.update m (Fin.last N, ρ) 0) := by sorry
