-- Prove2me | Theorems.Thm_Eden_planarAmplitude_at_one_all
-- name    : Eden.planarAmplitude_at_one_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:48.363976+00:00
-- url     : https://prove2.me/theorems/d828b5d7-d794-5a7c-bfec-3d538de9564d
-- title:
--   Eden: planar Amplitude at one all
-- statement:
--   The Eden construction uses the planar Amplitude at one all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusAngles.lean#L41-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusAngles.lean#L41-L46

import Definitions.Def_Eden_CircleOrbits
import Definitions.Def_Eden_TorusAngles
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.planarAmplitude_at_one_all (t : ℝ) : planarAmplitude t 1 = 1 := by sorry
