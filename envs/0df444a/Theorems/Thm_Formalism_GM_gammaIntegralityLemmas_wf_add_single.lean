-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_wf_add_single
-- name    : Formalism.GM.gammaIntegralityLemmas.wf_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:50.471808+00:00
-- url     : https://prove2.me/theorems/5663ac96-48f2-457c-8687-4f9ceba66024
-- title:
--   gamma Integrality Lemmas: wf add single
-- statement:
--   The gamma Integrality Lemmas construction uses the wf add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L287-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L287-L297

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.gammaIntegralityLemmas.wf_add_single (m : σ →₀ ℕ) (i : σ) :
    (wf (p := p) (m + Finsupp.single i 1)) = ((m i + 1 : ℕ) : ℚ_[p]) * wf m := by sorry
