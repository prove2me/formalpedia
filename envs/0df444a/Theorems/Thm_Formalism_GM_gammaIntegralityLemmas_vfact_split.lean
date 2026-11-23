-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vfact_split
-- name    : Formalism.GM.gammaIntegralityLemmas.vfact_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:07.323219+00:00
-- url     : https://prove2.me/theorems/617cf563-d5ac-4f63-9f40-5dc4576a805c
-- title:
--   gamma Integrality Lemmas: vfact split
-- statement:
--   The gamma Integrality Lemmas construction uses the vfact split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L212-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L212-L220

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

theorem Formalism.GM.gammaIntegralityLemmas.vfact_split {a b T B : ℕ} (h : a + b ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (a + b).factorial ≤ padicValNat p a.factorial + padicValNat p b.factorial + B := by sorry
