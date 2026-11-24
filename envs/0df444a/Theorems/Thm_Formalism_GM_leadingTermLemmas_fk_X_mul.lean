-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_X_mul
-- name    : Formalism.GM.leadingTermLemmas.fk_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:27.718107+00:00
-- url     : https://prove2.me/theorems/c6a16240-f6d1-4b14-a7f4-6c57291147a0
-- title:
--   leading Term Lemmas: fk X mul
-- statement:
--   The leading Term Lemmas construction uses the fk X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L91-L98

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

theorem Formalism.GM.leadingTermLemmas.fk_X_mul (i : σ) (g h : MvPolynomial σ K) : fk (X i * g) h = fk g (pderiv i h) := by sorry
