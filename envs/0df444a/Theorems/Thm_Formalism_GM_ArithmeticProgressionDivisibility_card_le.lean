-- Prove2me | Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_card_le
-- name    : Formalism.GM.ArithmeticProgressionDivisibility.card_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:26.254997+00:00
-- url     : https://prove2.me/theorems/428198ff-dcd7-4482-b14a-97492dff1f22
-- title:
--   Arithmetic Progression Divisibility: card le
-- statement:
--   The Arithmetic Progression Divisibility construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L134-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L134-L159

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

theorem Formalism.GM.ArithmeticProgressionDivisibility.card_le [IsUltrametricDist K] (ζ : K) (t₀ d : ℤ) (hd : IsCoprime d (p : ℤ)) (Y₀ i : ℕ) :
    (((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℝ)
      ≤ (Y₀ : ℝ) / (p : ℝ) ^ i + 1 := by sorry
