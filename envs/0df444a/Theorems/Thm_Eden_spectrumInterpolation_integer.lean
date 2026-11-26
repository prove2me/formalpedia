-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_integer
-- name    : Eden.spectrumInterpolation_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:27.93789+00:00
-- url     : https://prove2.me/theorems/3a2f4d69-2660-477a-aa48-233c36a4f325
-- title:
--   Eden: spectrum Interpolation integer
-- statement:
--   The Eden construction uses the spectrum Interpolation integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L42-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L42-L46

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.spectrumInterpolation_integer (a : Fin 5 → ℝ) {k : ℕ} (hk : k ≤ 5) :
    spectrumInterpolation a k = spectrumPartialSum a k := by sorry
