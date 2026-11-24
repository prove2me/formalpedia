-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_binK_eval_nat
-- name    : Formalism.GM.MeanGammaLemmas.binK_eval_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:27.272253+00:00
-- url     : https://prove2.me/theorems/9c7d0529-4266-4ed7-89c7-cc7484ec78dd
-- title:
--   Mean Gamma Lemmas: bin K eval nat
-- statement:
--   The Mean Gamma Lemmas construction uses the bin K eval nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L8-L13

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset

theorem Formalism.GM.MeanGammaLemmas.binK_eval_nat (F : Type) [Field F] [CharZero F] (k n : ℕ) :
    (binK F k).eval (n : F) = (n.choose k : F) := by sorry
