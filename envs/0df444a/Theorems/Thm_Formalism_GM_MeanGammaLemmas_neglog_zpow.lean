-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_neglog_zpow
-- name    : Formalism.GM.MeanGammaLemmas.neglog_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:50.106855+00:00
-- url     : https://prove2.me/theorems/998af9b6-2db4-4854-90e2-ca8d541871a4
-- title:
--   Mean Gamma Lemmas: neglog zpow
-- statement:
--   The Mean Gamma Lemmas construction uses the neglog zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L38-L42

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

theorem Formalism.GM.MeanGammaLemmas.neglog_zpow (p : ℕ) [hp : Fact p.Prime] (z : ℤ) : -Real.logb p ((p : ℝ) ^ (-z)) = z := by sorry
