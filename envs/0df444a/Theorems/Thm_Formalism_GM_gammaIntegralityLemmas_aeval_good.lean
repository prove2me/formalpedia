-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_good
-- name    : Formalism.GM.gammaIntegralityLemmas.aeval_good
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:58.345746+00:00
-- url     : https://prove2.me/theorems/b66fca54-2645-4b4c-8a4a-788768e2ef1b
-- title:
--   gamma Integrality Lemmas: aeval good
-- statement:
--   The gamma Integrality Lemmas construction uses the aeval good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L875-L888
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L875-L888

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

theorem Formalism.GM.gammaIntegralityLemmas.aeval_good (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    AllMono (p := p) (GoodQ ρ) ((LL.snoc LL.total).deg) (aeval (freezeSub p LL ρ) f) := by sorry
