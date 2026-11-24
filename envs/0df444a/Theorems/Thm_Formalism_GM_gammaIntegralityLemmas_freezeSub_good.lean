-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_freezeSub_good
-- name    : Formalism.GM.gammaIntegralityLemmas.freezeSub_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:56.705224+00:00
-- url     : https://prove2.me/theorems/2f84a6d8-65ec-47de-a409-8d96abdfe3fb
-- title:
--   gamma Integrality Lemmas: freeze Sub good
-- statement:
--   The gamma Integrality Lemmas construction uses the freeze Sub good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L785-L819
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L785-L819

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

theorem Formalism.GM.gammaIntegralityLemmas.freezeSub_good (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (i : Fin (N + 1)) (c : Fin r) :
    AllMono (p := p) (GoodQ ρ) (dv i) (freezeSub p LL ρ (i, c)) := by sorry
