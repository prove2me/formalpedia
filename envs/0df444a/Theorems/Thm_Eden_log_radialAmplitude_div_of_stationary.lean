-- Prove2me | Theorems.Thm_Eden_log_radialAmplitude_div_of_stationary
-- name    : Eden.log_radialAmplitude_div_of_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:13.352796+00:00
-- url     : https://prove2.me/theorems/656dd9f2-97f1-4620-bbdf-03906c408d6a
-- title:
--   Eden: log radial Amplitude div of stationary
-- statement:
--   The Eden construction uses the log radial Amplitude div of stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L32-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L32-L45

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_radialAmplitude_div_of_stationary {t s : ℝ} (ht : 0 < t)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    Real.log (radialAmplitude t s) / t = radialRate s := by sorry
