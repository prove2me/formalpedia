-- Prove2me | Theorems.Thm_Eden_hasDerivAt_radialAmplitude
-- name    : Eden.hasDerivAt_radialAmplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:18.991647+00:00
-- url     : https://prove2.me/theorems/2d1bf54b-896e-4469-a3b1-8cd7608cc8d3
-- title:
--   Eden: has Deriv At radial Amplitude
-- statement:
--   The radial factor has the manuscript's radial logarithmic growth rate.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L45-L59
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L45-L59

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.hasDerivAt_radialAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => radialAmplitude τ s)
      (radialRate (squaredRadiusEvolution t s) * radialAmplitude t s) t := by sorry
