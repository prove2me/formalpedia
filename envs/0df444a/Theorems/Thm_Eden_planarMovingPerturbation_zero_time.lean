-- Prove2me | Theorems.Thm_Eden_planarMovingPerturbation_zero_time
-- name    : Eden.planarMovingPerturbation_zero_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:07.285569+00:00
-- url     : https://prove2.me/theorems/22a16bba-363a-516c-9064-c694965fa7c6
-- title:
--   Eden: planar Moving Perturbation zero time
-- statement:
--   The Eden construction uses the planar Moving Perturbation zero time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L25-L29
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L25-L29

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarMovingPerturbation_zero_time (Ω : ℝ) (p v : PlanarSpace) :
    planarMovingPerturbation Ω 0 p v = v := by sorry
