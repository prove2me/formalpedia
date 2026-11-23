-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_of_norm_lt
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.dvd_of_norm_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:07.276543+00:00
-- url     : https://prove2.me/theorems/a44d2a96-6c08-4111-8240-6e193d12c86c
-- title:
--   Arithmetic Progression Divisibility: dvd of norm lt
-- statement:
--   The Arithmetic Progression Divisibility construction uses the dvd of norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L20-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L20-L44

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.dvd_of_norm_lt (k : ℤ) (i : ℕ) (hk : ‖(k : ℚ_[p])‖ < (p : ℝ) ^ (1 - (i : ℤ))) :
    (p ^ i : ℤ) ∣ k := by sorry
