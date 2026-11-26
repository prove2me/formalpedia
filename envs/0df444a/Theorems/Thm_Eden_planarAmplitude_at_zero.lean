-- Prove2me | Theorems.Thm_Eden_planarAmplitude_at_zero
-- name    : Eden.planarAmplitude_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:47.888376+00:00
-- url     : https://prove2.me/theorems/45c13920-6723-5ddf-b724-6d20ea83c599
-- title:
--   Eden: planar Amplitude at zero
-- statement:
--   The Eden construction uses the planar Amplitude at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L14-L17
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L14-L17

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarAmplitude_at_zero {t : ℝ} (ht : 0 ≤ t) :
    planarAmplitude t 0 = Real.exp (-2 * t) := by sorry
