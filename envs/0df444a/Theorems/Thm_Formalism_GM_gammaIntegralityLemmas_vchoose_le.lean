-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vchoose_le
-- name    : Formalism.GM.gammaIntegralityLemmas.vchoose_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:04.922719+00:00
-- url     : https://prove2.me/theorems/67c87685-5168-4330-be49-b889df7d6588
-- title:
--   gamma Integrality Lemmas: vchoose le
-- statement:
--   The gamma Integrality Lemmas construction uses the vchoose le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L207-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L207-L210

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.vchoose_le {t k T B : ℕ} (ht : t ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (t.choose k) ≤ B := by sorry
