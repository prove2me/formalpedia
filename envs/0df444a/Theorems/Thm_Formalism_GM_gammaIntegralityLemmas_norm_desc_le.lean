-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_desc_le
-- name    : Formalism.GM.gammaIntegralityLemmas.norm_desc_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:17.352127+00:00
-- url     : https://prove2.me/theorems/9c675a3f-61eb-4f30-b3fb-b14b793be45d
-- title:
--   gamma Integrality Lemmas: norm desc le
-- statement:
--   The gamma Integrality Lemmas construction uses the norm desc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L255-L259

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

theorem Formalism.GM.gammaIntegralityLemmas.norm_desc_le (x a : ℕ) : ‖((x.descFactorial a : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ)) := by sorry
