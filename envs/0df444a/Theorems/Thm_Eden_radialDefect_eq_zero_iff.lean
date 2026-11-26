-- Prove2me | Theorems.Thm_Eden_radialDefect_eq_zero_iff
-- name    : Eden.radialDefect_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:38.038711+00:00
-- url     : https://prove2.me/theorems/61729f3e-e471-4383-965a-ef3ad2706c32
-- title:
--   Eden: radial Defect eq zero iff
-- statement:
--   The Eden construction uses the radial Defect eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L46-L53
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L46-L53

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialDefect_eq_zero_iff {t s : ℝ} (ht : 0 < t) :
    radialDefect t s = 0 ↔ s = 1 := by sorry
