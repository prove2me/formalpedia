-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_cancel
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.dvd_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:12.406634+00:00
-- url     : https://prove2.me/theorems/fc368d2f-e6e5-4363-b82a-e1cd41c19462
-- title:
--   Arithmetic Progression Divisibility: dvd cancel
-- statement:
--   The Arithmetic Progression Divisibility construction uses the dvd cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L109-L110

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.dvd_cancel {d : ℤ} (hd : IsCoprime d (p : ℤ)) (i : ℕ) {m : ℤ} (hm : (p : ℤ) ^ i ∣ d * m) :
    (p : ℤ) ^ i ∣ m := by sorry
