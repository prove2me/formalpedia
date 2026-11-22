-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_amgm_period_lattice_bound
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:36.975566+00:00
-- url     : https://prove2.me/theorems/dac6b4ae-8389-48ee-a6ef-7fe129e49ce2
-- title:
--   flip Two Three: amgm period lattice bound
-- statement:
--   The flip Two Three construction uses the amgm period lattice bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L114-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L114-L135

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound : AmgmSumLowerBoundOfProd := by sorry
