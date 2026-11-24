-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_vchoose_le
-- name    : Formalism.GM.MeanGammaLemmas.vchoose_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:48.596269+00:00
-- url     : https://prove2.me/theorems/bfad8793-fdbf-4fc2-bab4-a91e8df59b94
-- title:
--   Mean Gamma Lemmas: vchoose le
-- statement:
--   The Mean Gamma Lemmas construction uses the vchoose le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L237-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L237-L241

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

theorem Formalism.GM.MeanGammaLemmas.vchoose_le (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) :
    (padicValNat p (n.choose k) : ℝ) ≤ (Nat.log p n : ℝ) := by sorry
