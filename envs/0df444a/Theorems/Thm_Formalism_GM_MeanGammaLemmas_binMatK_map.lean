-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_binMatK_map
-- name    : Formalism.GM.MeanGammaLemmas.binMatK_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:54.511941+00:00
-- url     : https://prove2.me/theorems/d1312437-4195-4146-804d-6371bf91ab89
-- title:
--   Mean Gamma Lemmas: bin Mat K map
-- statement:
--   The Mean Gamma Lemmas construction uses the bin Mat K map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L19-L23

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

theorem Formalism.GM.MeanGammaLemmas.binMatK_map (F L : Type) [Field F] [Field L] (φ : F →+* L) {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) :
    binMatK L del (fun i j k => φ (c i j k)) = (binMatK F del c).map (Polynomial.map φ) := by sorry
