-- Prove2me | Theorems.Thm_Eden_radialAmplitude_at_zero
-- name    : Eden.radialAmplitude_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:55.560986+00:00
-- url     : https://prove2.me/theorems/e6ab3886-2bfe-5dd1-91ba-64ae4eff863c
-- title:
--   Eden: radial Amplitude at zero
-- statement:
--   The Eden construction uses the radial Amplitude at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L19-L22
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L19-L22

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialAmplitude_at_zero {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 0 = Real.exp (-2 * t) := by sorry
