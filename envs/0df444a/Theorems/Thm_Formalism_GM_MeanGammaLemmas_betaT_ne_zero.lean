-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_betaT_ne_zero
-- name    : Formalism.GM.MeanGammaLemmas.betaT_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:17.797812+00:00
-- url     : https://prove2.me/theorems/f4b06c89-d94f-4869-9f0e-8af882b763fd
-- title:
--   Mean Gamma Lemmas: beta T ne zero
-- statement:
--   The Mean Gamma Lemmas construction uses the beta T ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L391-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L391-L398

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
open Polynomial Finset Formalism.GM.M

theorem Formalism.GM.MeanGammaLemmas.betaT_ne_zero (p : ℕ) [hp : Fact p.Prime] (m z o S e : ℕ) : betaT p m z o S e ≠ 0 := by sorry
