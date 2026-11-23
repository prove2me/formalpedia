-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_int
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.norm_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:07.019805+00:00
-- url     : https://prove2.me/theorems/60d21503-2340-4648-8828-c6cb4d0891ee
-- title:
--   Arithmetic Progression Divisibility: norm int
-- statement:
--   The Arithmetic Progression Divisibility construction uses the norm int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L11-L12

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.norm_int (k : ℤ) : ‖(k : K)‖ = ‖(k : ℚ_[p])‖ := by sorry
