-- Prove2me | Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
-- name    : Eden.continuousOn_squaredRadiusEvolution_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:49.659822+00:00
-- url     : https://prove2.me/theorems/eebd0002-2dbe-4fa6-a570-5102d0a2ccc6
-- title:
--   Eden: continuous On squared Radius Evolution time
-- statement:
--   The Eden construction uses the continuous On squared Radius Evolution time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L78-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L78-L80

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuousOn_squaredRadiusEvolution_time (s : ℝ) :
    ContinuousOn (fun t => squaredRadiusEvolution t s) (Ici 0) := by sorry
