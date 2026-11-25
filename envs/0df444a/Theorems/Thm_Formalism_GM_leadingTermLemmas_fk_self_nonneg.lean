-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_self_nonneg
-- name    : Formalism.GM.leadingTermLemmas.fk_self_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:43.907741+00:00
-- url     : https://prove2.me/theorems/ac1e8e57-a0ec-44b6-8692-a84acca6edc6
-- title:
--   leading Term Lemmas: fk self nonneg
-- statement:
--   The leading Term Lemmas construction uses the fk self nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L129-L130

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.leadingTermLemmas.fk_self_nonneg (F : MvPolynomial σ ℝ) : 0 ≤ fk F F := by sorry
