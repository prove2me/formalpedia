-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_eq
-- name    : Eden.periodicGlobalGrowthInterpolation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:46.035507+00:00
-- url     : https://prove2.me/theorems/67f651a8-a574-5a01-a7c2-65adb318126c
-- title:
--   Eden: periodic Global Growth Interpolation eq
-- statement:
--   The Eden construction uses the periodic Global Growth Interpolation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L35-L37
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L35-L37

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthInterpolation_eq {c : ℝ} (hc : 4 < c) (d : ℝ) :
    periodicGlobalGrowthInterpolation c d = spectrumInterpolation ![2, 0, -2, -2, -c] d := by sorry
