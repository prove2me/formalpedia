-- Prove2me | Theorems.Thm_Eden_planarMovingPerturbation_eq
-- name    : Eden.planarMovingPerturbation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:54.795602+00:00
-- url     : https://prove2.me/theorems/69c1306b-fc47-4170-85ee-c4545bed418b
-- title:
--   Eden: planar Moving Perturbation eq
-- statement:
--   The Eden construction uses the planar Moving Perturbation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L21-L23
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L21-L23

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarMovingPerturbation_eq (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    planarMovingPerturbation Ω t p v = planarDiagonal (planarFactors t p) v := by sorry
