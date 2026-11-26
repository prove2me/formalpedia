-- Prove2me | Theorems.Thm_Eden_planarAmplitude_eq_exp_integral
-- name    : Eden.planarAmplitude_eq_exp_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:15.917895+00:00
-- url     : https://prove2.me/theorems/5983f4a1-b9b4-5c94-9bb7-04681085b683
-- title:
--   Eden: planar Amplitude eq exp integral
-- statement:
--   The tangential factor is the exponential integral of the tangential rate.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L109-L112
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L109-L112

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.planarAmplitude_eq_exp_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) := by sorry
