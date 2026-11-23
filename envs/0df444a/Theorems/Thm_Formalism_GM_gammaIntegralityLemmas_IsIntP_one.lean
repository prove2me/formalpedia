-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_one
-- name    : Formalism.GM.gammaIntegralityLemmas.IsIntP.one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:46.189817+00:00
-- url     : https://prove2.me/theorems/523543d6-6bec-46f3-999a-e40699f59501
-- title:
--   Is Int P: one
-- statement:
--   The Is Int P construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L720-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L720-L721

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

theorem Formalism.GM.gammaIntegralityLemmas.IsIntP.one : IsIntP (1 : MvPolynomial σ ℚ_[p]) := by sorry
