-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_negLog_beta
-- name    : Formalism.GM.MeanGammaLemmas.negLog_beta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:41.633525+00:00
-- url     : https://prove2.me/theorems/c8e25fc9-770f-45aa-8283-75de25fb814a
-- title:
--   Mean Gamma Lemmas: neg Log beta
-- statement:
--   The Mean Gamma Lemmas construction uses the neg Log beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L248-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L248-L264

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
open Finset

theorem Formalism.GM.MeanGammaLemmas.negLog_beta (p : ℕ) [hp : Fact p.Prime] (M e z o S : ℕ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ M * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ =
      (M : ℝ) + padicValNat p e.factorial + padicValNat p ((z + e).choose e) -
        padicValNat p o.factorial - padicValNat p S.factorial := by sorry
