-- Prove2me | Theorems.Thm_Eden_log_radialAmplitude_lower_bound
-- name    : Eden.log_radialAmplitude_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:53.238556+00:00
-- url     : https://prove2.me/theorems/b6893c48-f311-4ee2-a990-8d64cf08f11c
-- title:
--   Eden: log radial Amplitude lower bound
-- statement:
--   The Eden construction uses the log radial Amplitude lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L25-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L25-L34

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.log_radialAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : -4 * t ≤ Real.log (radialAmplitude t s) := by sorry
