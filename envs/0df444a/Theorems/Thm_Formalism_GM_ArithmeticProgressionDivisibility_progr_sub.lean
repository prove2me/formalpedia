-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_progr_sub
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.progr_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:13.816979+00:00
-- url     : https://prove2.me/theorems/a84de531-4b59-4bbc-b3f3-a79be7af2a40
-- title:
--   Arithmetic Progression Divisibility: progr sub
-- statement:
--   The Arithmetic Progression Divisibility construction uses the progr sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L113-L115

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.progr_sub (t₀ d : ℤ) (a b : ℕ) : progr t₀ d a - progr t₀ d b = d * ((a : ℤ) - b) := by sorry
