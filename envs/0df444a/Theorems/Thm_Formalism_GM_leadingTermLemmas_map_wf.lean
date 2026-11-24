-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_map_wf
-- name    : Formalism.GM.leadingTermLemmas.map_wf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:49.220811+00:00
-- url     : https://prove2.me/theorems/d62fb5aa-d8dd-428a-b878-ac0b8dc593dd
-- title:
--   leading Term Lemmas: map wf
-- statement:
--   The leading Term Lemmas construction uses the map wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1777-L1778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1777-L1778

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
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.leadingTermLemmas.map_wf (m : σ →₀ ℕ) : ι (wf m) = (wf m : K) := by sorry
