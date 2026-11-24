-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_gamma_term
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.gamma_term
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:04.734804+00:00
-- url     : https://prove2.me/theorems/2f2961ad-9d1f-4ed2-9d4b-185eca69915f
-- title:
--   flip Two Three: gamma term
-- statement:
--   The flip Two Three construction uses the gamma term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L56-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L56-L75

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.gamma_term (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-Real.pi * u)) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0:ℝ), u ^ k * Real.exp (-Real.pi * u) = (k.factorial : ℝ) / Real.pi ^ (k+1) := by sorry
