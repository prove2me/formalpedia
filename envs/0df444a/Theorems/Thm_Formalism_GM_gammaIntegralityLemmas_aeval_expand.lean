-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_expand
-- name    : Formalism.GM.gammaIntegralityLemmas.aeval_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:44.939671+00:00
-- url     : https://prove2.me/theorems/7b2e23d1-914f-4a46-aa50-441723032b8a
-- title:
--   gamma Integrality Lemmas: aeval expand
-- statement:
--   The gamma Integrality Lemmas construction uses the aeval expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L866-L873
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L866-L873

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
variable {N r : ℕ}

theorem Formalism.GM.gammaIntegralityLemmas.aeval_expand (LL : Letters (N + 1)) (ρ : Fin r) (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    aeval (freezeSub p LL ρ) f = ∑ μ ∈ f.support,
      C (coeff μ f) * ∏ v : Fin (N + 1) × Fin r, freezeSub p LL ρ v ^ μ v := by sorry
