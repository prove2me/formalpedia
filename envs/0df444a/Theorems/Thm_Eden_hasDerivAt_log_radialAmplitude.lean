-- Prove2me | Theorems.Thm_Eden_hasDerivAt_log_radialAmplitude
-- name    : Eden.hasDerivAt_log_radialAmplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:36.160804+00:00
-- url     : https://prove2.me/theorems/be735e35-fcd3-4ecc-818d-95a73e9bb9cc
-- title:
--   Eden: has Deriv At log radial Amplitude
-- statement:
--   The Eden construction uses the has Deriv At log radial Amplitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L71-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L71-L76

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.hasDerivAt_log_radialAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => Real.log (radialAmplitude τ s))
      (radialRate (squaredRadiusEvolution t s)) t := by sorry
