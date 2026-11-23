-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_prod_eq_wf
-- name    : Formalism.GM.gammaIntegralityLemmas.prod_eq_wf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:59.711982+00:00
-- url     : https://prove2.me/theorems/6bf6ed13-d4c9-450e-8ac1-7770d3ef0f3f
-- title:
--   gamma Integrality Lemmas: prod eq wf
-- statement:
--   The gamma Integrality Lemmas construction uses the prod eq wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L284-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L284-L285

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

theorem Formalism.GM.gammaIntegralityLemmas.prod_eq_wf (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) = wf (p := p) m := by sorry
