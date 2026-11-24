-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_fact
-- name    : Formalism.GM.gammaIntegralityLemmas.norm_fact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:56.445563+00:00
-- url     : https://prove2.me/theorems/8beb18e9-40be-4319-889b-0df7bd411092
-- title:
--   gamma Integrality Lemmas: norm fact
-- statement:
--   The gamma Integrality Lemmas construction uses the norm fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L252-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L252-L253

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

theorem Formalism.GM.gammaIntegralityLemmas.norm_fact (t : ℕ) : ‖(t.factorial : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t.factorial : ℤ)) := by sorry
