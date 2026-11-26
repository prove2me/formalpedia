-- Prove2me | Theorems.Thm_Eden_log_planarAmplitude_lower_bound
-- name    : Eden.log_planarAmplitude_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:47.39006+00:00
-- url     : https://prove2.me/theorems/4c9fcd43-eab5-4808-bd14-cbdeb050173c
-- title:
--   Eden: log planar Amplitude lower bound
-- statement:
--   The Eden construction uses the log planar Amplitude lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L36-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L36-L45

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_planarAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : -2 * t ≤ Real.log (planarAmplitude t s) := by sorry
