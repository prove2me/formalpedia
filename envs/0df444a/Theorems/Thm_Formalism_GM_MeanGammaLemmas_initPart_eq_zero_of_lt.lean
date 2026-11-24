-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_initPart_eq_zero_of_lt
-- name    : Formalism.GM.MeanGammaLemmas.initPart_eq_zero_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:55.616369+00:00
-- url     : https://prove2.me/theorems/2070943c-3f19-45c6-a165-8ba7578c64ed
-- title:
--   Mean Gamma Lemmas: init Part eq zero of lt
-- statement:
--   The Mean Gamma Lemmas construction uses the init Part eq zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L81-L90

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

theorem Formalism.GM.MeanGammaLemmas.initPart_eq_zero_of_lt (v : σ) (e o : ℕ) (f : MvPolynomial σ ℚ_[p]) (hf : HasOrder v o f) (h : e < o) :
    initPart v e f = 0 := by sorry
