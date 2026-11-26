-- Prove2me | Theorems.Thm_Eden_planarAmplitude_at_one
-- name    : Eden.planarAmplitude_at_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:02.302183+00:00
-- url     : https://prove2.me/theorems/357262f2-e61e-50e2-8fd3-8fdc5bf991ee
-- title:
--   Eden: planar Amplitude at one
-- statement:
--   The Eden construction uses the planar Amplitude at one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L24-L27
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L24-L27

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarAmplitude_at_one {t : ℝ} (ht : 0 ≤ t) : planarAmplitude t 1 = 1 := by sorry
