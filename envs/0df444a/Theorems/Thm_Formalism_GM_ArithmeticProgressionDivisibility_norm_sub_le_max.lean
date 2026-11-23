-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_sub_le_max
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.norm_sub_le_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:16.653003+00:00
-- url     : https://prove2.me/theorems/cedaf15f-cf07-4c5d-9b21-133554cdd9fd
-- title:
--   Arithmetic Progression Divisibility: norm sub le max
-- statement:
--   The Arithmetic Progression Divisibility construction uses the norm sub le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L15-L17

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
omit [NormedAlgebra ℚ_[p] K]

theorem Formalism.GM.ArithmeticProgressionDivisibility.norm_sub_le_max [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry
