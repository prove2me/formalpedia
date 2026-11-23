-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_map
-- name    : Formalism.GM.leadingTermLemmas.fk_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:29.420427+00:00
-- url     : https://prove2.me/theorems/797074d0-a383-4522-8b7f-e9bf5d0a3ccc
-- title:
--   leading Term Lemmas: fk map
-- statement:
--   The leading Term Lemmas construction uses the fk map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1780-L1784
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1780-L1784

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

theorem Formalism.GM.leadingTermLemmas.fk_map (F G : MvPolynomial σ ℚ) : fk (map ι F) (map ι G) = ι (fk F G) := by sorry
