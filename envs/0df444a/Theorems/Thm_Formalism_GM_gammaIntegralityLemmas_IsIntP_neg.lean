-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_neg
-- name    : Formalism.GM.gammaIntegralityLemmas.IsIntP.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:47.449508+00:00
-- url     : https://prove2.me/theorems/b297fde9-d9f4-462a-abdd-9512f79c2740
-- title:
--   Is Int P: neg
-- statement:
--   The Is Int P construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L711-L712
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L711-L712

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

theorem Formalism.GM.gammaIntegralityLemmas.IsIntP.neg {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) : IsIntP (-P) := by sorry
