-- Prove2me | Theorems.Thm_Eden_radialAmplitude_at_two
-- name    : Eden.radialAmplitude_at_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:56.753017+00:00
-- url     : https://prove2.me/theorems/266295cf-559f-4db8-ae85-3e5e51856397
-- title:
--   Eden: radial Amplitude at two
-- statement:
--   The Eden construction uses the radial Amplitude at two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L40-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L40-L44

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialAmplitude_at_two {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 2 = Real.exp (-4 * t) := by sorry
