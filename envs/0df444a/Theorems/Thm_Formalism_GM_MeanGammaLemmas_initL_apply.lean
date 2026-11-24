-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_initL_apply
-- name    : Formalism.GM.MeanGammaLemmas.initL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:45.532809+00:00
-- url     : https://prove2.me/theorems/ac419848-c9de-4004-8cd7-3e61e882b266
-- title:
--   Mean Gamma Lemmas: init L apply
-- statement:
--   The Mean Gamma Lemmas construction uses the init L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L79-L79

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem Formalism.GM.MeanGammaLemmas.initL_apply (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : initL p v e f = initPart v e f := by sorry
