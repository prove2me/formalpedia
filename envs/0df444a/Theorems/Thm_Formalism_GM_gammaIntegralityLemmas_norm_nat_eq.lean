-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_nat_eq
-- name    : Formalism.GM.gammaIntegralityLemmas.norm_nat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:09.243695+00:00
-- url     : https://prove2.me/theorems/03b06a82-330c-4e21-b3c6-3452548d790e
-- title:
--   gamma Integrality Lemmas: norm nat eq
-- statement:
--   The gamma Integrality Lemmas construction uses the norm nat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L241-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L241-L242

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

theorem Formalism.GM.gammaIntegralityLemmas.norm_nat_eq (t : ℕ) (ht : t ≠ 0) : ‖(t : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t : ℤ)) := by sorry
