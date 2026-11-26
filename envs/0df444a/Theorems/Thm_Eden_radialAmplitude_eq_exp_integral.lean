-- Prove2me | Theorems.Thm_Eden_radialAmplitude_eq_exp_integral
-- name    : Eden.radialAmplitude_eq_exp_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:21.157086+00:00
-- url     : https://prove2.me/theorems/38ec926f-3aab-5e14-a8fe-3cc738fe5a8e
-- title:
--   Eden: radial Amplitude eq exp integral
-- statement:
--   The radial factor is the exponential integral of the radial rate.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L115-L118
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L115-L118

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialAmplitude_eq_exp_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by sorry
