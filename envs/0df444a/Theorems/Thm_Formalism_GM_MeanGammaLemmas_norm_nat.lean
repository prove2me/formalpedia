-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_norm_nat
-- name    : Formalism.GM.MeanGammaLemmas.norm_nat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:57.913829+00:00
-- url     : https://prove2.me/theorems/f79bada0-940d-4329-9998-f0117027f16e
-- title:
--   Mean Gamma Lemmas: norm nat
-- statement:
--   The Mean Gamma Lemmas construction uses the norm nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L30-L36

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

theorem Formalism.GM.MeanGammaLemmas.norm_nat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by sorry
