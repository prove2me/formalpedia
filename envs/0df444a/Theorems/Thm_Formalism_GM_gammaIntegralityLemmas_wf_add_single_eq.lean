-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_wf_add_single_eq
-- name    : Formalism.GM.gammaIntegralityLemmas.wf_add_single_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:38.391812+00:00
-- url     : https://prove2.me/theorems/e4cd61d9-88b0-451f-9536-e38f8f44bf1d
-- title:
--   gamma Integrality Lemmas: wf add single eq
-- statement:
--   The gamma Integrality Lemmas construction uses the wf add single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L918-L927
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L918-L927

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.wf_add_single_eq (δ : σ →₀ ℕ) (y : σ) (t : ℕ) :
    wf (p := p) (δ + Finsupp.single y t) * ((δ y).factorial : ℚ_[p]) = wf δ * ((δ y + t).factorial : ℚ_[p]) := by sorry
