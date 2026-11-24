-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_vfact_le
-- name    : Formalism.GM.MeanGammaLemmas.vfact_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:58.462069+00:00
-- url     : https://prove2.me/theorems/e9240dfe-ebc1-47cd-8bf1-203c9c6bed85
-- title:
--   Mean Gamma Lemmas: vfact le
-- statement:
--   The Mean Gamma Lemmas construction uses the vfact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L182-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L182-L193

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

theorem Formalism.GM.MeanGammaLemmas.vfact_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ n / ((p : ℝ) - 1) := by sorry
