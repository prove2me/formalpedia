-- Prove2me | Theorems.Thm_Eden_log_planarAmplitude_div_of_stationary
-- name    : Eden.log_planarAmplitude_div_of_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:53.244426+00:00
-- url     : https://prove2.me/theorems/a57b6485-e751-5c19-8802-0ed1c0da4978
-- title:
--   Eden: log planar Amplitude div of stationary
-- statement:
--   The Eden construction uses the log planar Amplitude div of stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L19-L30
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L19-L30

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_planarAmplitude_div_of_stationary {t s : ℝ} (ht : 0 < t)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    Real.log (planarAmplitude t s) / t = tangentialRate s := by sorry
