-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_neg_logb_zpow_self
-- name    : Formalism.GM.MeanGammaLemmas.neg_logb_zpow_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:10.017871+00:00
-- url     : https://prove2.me/theorems/fe9fed8c-f2fc-42c8-8916-48b19d3cb070
-- title:
--   Mean Gamma Lemmas: neg logb zpow self
-- statement:
--   The Mean Gamma Lemmas construction uses the neg logb zpow self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L243-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L243-L246

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

theorem Formalism.GM.MeanGammaLemmas.neg_logb_zpow_self (p : ℕ) [hp : Fact p.Prime] (z : ℤ) : -Real.logb p ((p : ℝ) ^ z) = -z := by sorry
