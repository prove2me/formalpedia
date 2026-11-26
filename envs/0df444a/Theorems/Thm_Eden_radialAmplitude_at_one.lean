-- Prove2me | Theorems.Thm_Eden_radialAmplitude_at_one
-- name    : Eden.radialAmplitude_at_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:15.46008+00:00
-- url     : https://prove2.me/theorems/c2eae30c-acb8-4ede-b14f-e10183ba33c2
-- title:
--   Eden: radial Amplitude at one
-- statement:
--   The Eden construction uses the radial Amplitude at one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L29-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L29-L33

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialAmplitude_at_one {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 1 = Real.exp (2 * t) := by sorry
