-- Prove2me | Theorems.Thm_Eden_log_radialAmplitude_eq_integral
-- name    : Eden.log_radialAmplitude_eq_integral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:12.728395+00:00
-- url     : https://prove2.me/theorems/5a3f424d-d226-509c-9960-89b687aa1fe1
-- title:
--   Eden: log radial Amplitude eq integral
-- statement:
--   The Eden construction uses the log radial Amplitude eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L95-L106
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L95-L106

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_radialAmplitude_eq_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) := by sorry
