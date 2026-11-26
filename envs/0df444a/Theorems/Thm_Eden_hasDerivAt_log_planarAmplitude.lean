-- Prove2me | Theorems.Thm_Eden_hasDerivAt_log_planarAmplitude
-- name    : Eden.hasDerivAt_log_planarAmplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:21.35422+00:00
-- url     : https://prove2.me/theorems/4a313b14-3797-53d7-acef-5f29cd0059ce
-- title:
--   Eden: has Deriv At log planar Amplitude
-- statement:
--   The Eden construction uses the has Deriv At log planar Amplitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L64-L69
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L64-L69

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.hasDerivAt_log_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => Real.log (planarAmplitude τ s))
      (tangentialRate (squaredRadiusEvolution t s)) t := by sorry
