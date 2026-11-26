-- Prove2me | Theorems.Thm_Eden_frequencyFiniteTimeDimension_isGreatest
-- name    : Eden.frequencyFiniteTimeDimension_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:57.239165+00:00
-- url     : https://prove2.me/theorems/15386966-cd64-4148-adee-7d240f03ee45
-- title:
--   Eden: frequency Finite Time Dimension is Greatest
-- statement:
--   The Eden construction uses the frequency Finite Time Dimension is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L106-L110
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L106-L110

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.frequencyFiniteTimeDimension_isGreatest {c t : ℝ} (hc : 4 < c) (ν : ℝ)
    (ht : 0 < t) :
    IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (targetDimension c) := by sorry
