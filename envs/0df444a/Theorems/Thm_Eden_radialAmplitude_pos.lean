-- Prove2me | Theorems.Thm_Eden_radialAmplitude_pos
-- name    : Eden.radialAmplitude_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:39.579266+00:00
-- url     : https://prove2.me/theorems/01ba2aef-c433-401c-8e40-ac25bec32c95
-- title:
--   Eden: radial Amplitude pos
-- statement:
--   The Eden construction uses the radial Amplitude pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L40-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L40-L44

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialAmplitude_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < radialAmplitude t s := by sorry
