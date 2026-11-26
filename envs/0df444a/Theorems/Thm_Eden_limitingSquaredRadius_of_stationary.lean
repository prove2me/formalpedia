-- Prove2me | Theorems.Thm_Eden_limitingSquaredRadius_of_stationary
-- name    : Eden.limitingSquaredRadius_of_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:16.855864+00:00
-- url     : https://prove2.me/theorems/4aa60860-7b69-451d-b10f-5548d0c8544d
-- title:
--   Eden: limiting Squared Radius of stationary
-- statement:
--   The Eden construction uses the limiting Squared Radius of stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L47-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L47-L49

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.limitingSquaredRadius_of_stationary {s : ℝ} (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    limitingSquaredRadius s = s := by sorry
