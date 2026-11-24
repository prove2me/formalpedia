-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_vmin_le
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.vmin_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:14.984857+00:00
-- url     : https://prove2.me/theorems/840f0075-ceed-4cd7-a8be-81fd3da800fc
-- title:
--   Arithmetic Progression Divisibility: vmin le
-- statement:
--   The Arithmetic Progression Divisibility construction uses the vmin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L47-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L47-L105

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.vmin_le (h : ℕ) (x : K) :
    vmin p h x ≤ ∑ i ∈ Icc 1 h, (if ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) := by sorry
