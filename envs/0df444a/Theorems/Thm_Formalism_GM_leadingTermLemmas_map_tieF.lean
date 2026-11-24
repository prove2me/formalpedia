-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_map_tieF
-- name    : Formalism.GM.leadingTermLemmas.map_tieF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:57.501068+00:00
-- url     : https://prove2.me/theorems/d80cb740-1dc1-4df5-9d06-03c532c1f041
-- title:
--   leading Term Lemmas: map tie F
-- statement:
--   The leading Term Lemmas construction uses the map tie F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1750-L1751
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1750-L1751

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

theorem Formalism.GM.leadingTermLemmas.map_tieF (g : MvPolynomial σ ℚ) : map ι (tieF w e g) = tieF w e (map ι g) := by sorry
