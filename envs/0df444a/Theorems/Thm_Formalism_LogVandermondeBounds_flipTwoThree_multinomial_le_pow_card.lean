-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_multinomial_le_pow_card
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.multinomial_le_pow_card
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:55.585182+00:00
-- url     : https://prove2.me/theorems/630b97d6-6736-4c9f-86d0-098b7999aa28
-- title:
--   flip Two Three: multinomial le pow card
-- statement:
--   The flip Two Three construction uses the multinomial le pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L231-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L231-L249

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory

theorem Formalism.LogVandermondeBounds.flipTwoThree.multinomial_le_pow_card : MultinomialPowerBound := by sorry
