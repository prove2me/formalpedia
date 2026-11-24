-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_binMatK_eval_nat
-- name    : Formalism.GM.MeanGammaLemmas.binMatK_eval_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:26.272424+00:00
-- url     : https://prove2.me/theorems/05a72fda-7b61-4aa8-8f54-e0e1d54e9d81
-- title:
--   Mean Gamma Lemmas: bin Mat K eval nat
-- statement:
--   The Mean Gamma Lemmas construction uses the bin Mat K eval nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L25-L28

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

theorem Formalism.GM.MeanGammaLemmas.binMatK_eval_nat (F : Type) [Field F] [CharZero F] {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) (i j : Fin n) (t : ℕ) :
    (binMatK F del c i j).eval (t : F) = ∑ k ∈ range (del + 1), c i j k * (t.choose k : F) := by sorry
