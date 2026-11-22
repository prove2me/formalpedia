-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_apply
-- name    : Formalism.GM.gammaIntegralityLemmas.Dop_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:15.634092+00:00
-- url     : https://prove2.me/theorems/3ed767ff-8d28-4374-8d90-b7c76d748862
-- title:
--   gamma Integrality Lemmas: Dop apply
-- statement:
--   The gamma Integrality Lemmas construction uses the Dop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L405-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L405-L405

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

theorem Formalism.GM.gammaIntegralityLemmas.Dop_apply (u v : σ) (q : MvPolynomial σ ℚ_[p]) : Dop u v q = pderiv u (pderiv v q) := by sorry
