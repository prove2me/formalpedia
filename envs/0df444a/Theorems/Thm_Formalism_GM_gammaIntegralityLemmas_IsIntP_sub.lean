-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sub
-- name    : Formalism.GM.gammaIntegralityLemmas.IsIntP.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:44.118226+00:00
-- url     : https://prove2.me/theorems/59dc4de7-ffa5-43f8-b49c-d0f1f734940a
-- title:
--   Is Int P: sub
-- statement:
--   The Is Int P construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L714-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L714-L715

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

theorem Formalism.GM.gammaIntegralityLemmas.IsIntP.sub {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P - P') := by sorry
