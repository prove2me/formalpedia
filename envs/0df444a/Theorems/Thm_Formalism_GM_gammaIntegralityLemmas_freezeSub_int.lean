-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_freezeSub_int
-- name    : Formalism.GM.gammaIntegralityLemmas.freezeSub_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:02.512165+00:00
-- url     : https://prove2.me/theorems/f5c61afd-061a-41d1-9b7f-e2c9d42df209
-- title:
--   gamma Integrality Lemmas: freeze Sub int
-- statement:
--   The gamma Integrality Lemmas construction uses the freeze Sub int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L821-L829
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L821-L829

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

theorem Formalism.GM.gammaIntegralityLemmas.freezeSub_int (LL : Letters (N + 1)) (ρ : Fin r) (v : Fin (N + 1) × Fin r) :
    IsIntP (freezeSub p LL ρ v) := by sorry
