-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ExponentialIntegralMeasures_integral_exp_int
-- name    : Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures.integral_exp_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:45.525876+00:00
-- url     : https://prove2.me/theorems/3261f9c4-abfe-41a1-b371-d7dd8b3eb3de
-- title:
--   Exponential Integral Measures: integral exp int
-- statement:
--   The Exponential Integral Measures construction uses the integral exp int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/IntegralExpInt.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/IntegralExpInt.lean#L9-L19

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures

theorem Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures.integral_exp_int (k : ℤ) :
    ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi), Complex.exp ((k : ℂ) * I * (θ : ℂ)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by sorry
