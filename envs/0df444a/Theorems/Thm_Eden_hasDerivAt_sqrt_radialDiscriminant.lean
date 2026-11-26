-- Prove2me | Theorems.Thm_Eden_hasDerivAt_sqrt_radialDiscriminant
-- name    : Eden.hasDerivAt_sqrt_radialDiscriminant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:20.86003+00:00
-- url     : https://prove2.me/theorems/c47e5d15-58e3-580c-ba50-579f0f9ebc3e
-- title:
--   Eden: has Deriv At sqrt radial Discriminant
-- statement:
--   The Eden construction uses the has Deriv At sqrt radial Discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L23-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GrowthRates.lean#L23-L42

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.hasDerivAt_sqrt_radialDiscriminant {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => Real.sqrt (radialDiscriminant τ s))
      (-2 * (1 - (squaredRadiusEvolution t s - 1) ^ 2) *
        Real.sqrt (radialDiscriminant t s)) t := by sorry
