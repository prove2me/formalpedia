-- Prove2me | Theorems.Thm_Eden_radialDefect_pos
-- name    : Eden.radialDefect_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:02.742106+00:00
-- url     : https://prove2.me/theorems/057f1017-e892-413e-807f-c38462858ecd
-- title:
--   Eden: radial Defect pos
-- statement:
--   The Eden construction uses the radial Defect pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L36-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L36-L44

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialDefect_pos {t s : ℝ} (ht : 0 < t) (hs : s ≠ 1) :
    0 < radialDefect t s := by sorry
