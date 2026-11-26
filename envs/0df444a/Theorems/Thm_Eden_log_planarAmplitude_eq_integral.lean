-- Prove2me | Theorems.Thm_Eden_log_planarAmplitude_eq_integral
-- name    : Eden.log_planarAmplitude_eq_integral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:51.162818+00:00
-- url     : https://prove2.me/theorems/c7d267c3-8da9-43c9-bc82-d9a0651129f9
-- title:
--   Eden: log planar Amplitude eq integral
-- statement:
--   The Eden construction uses the log planar Amplitude eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L82-L93
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L82-L93

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_planarAmplitude_eq_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) := by sorry
