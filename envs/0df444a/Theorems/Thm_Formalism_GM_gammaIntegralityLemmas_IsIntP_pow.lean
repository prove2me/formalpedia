-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_pow
-- name    : Formalism.GM.gammaIntegralityLemmas.IsIntP.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:49.451259+00:00
-- url     : https://prove2.me/theorems/03c97fb7-c9b4-4320-8ef8-bb1f85fb9ab8
-- title:
--   Is Int P: pow
-- statement:
--   The Is Int P construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L738-L741
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L738-L741

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.IsIntP.pow {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (n : ℕ) : IsIntP (P ^ n) := by sorry
