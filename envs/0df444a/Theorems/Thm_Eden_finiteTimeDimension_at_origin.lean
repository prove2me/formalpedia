-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_at_origin
-- name    : Eden.finiteTimeDimension_at_origin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:22:50.522388+00:00
-- url     : https://prove2.me/theorems/ed839daa-f544-47cc-a227-299b54d9f44b
-- title:
--   Eden: finite Time Dimension at origin
-- statement:
--   The Eden construction uses the finite Time Dimension at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L146-L152
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L146-L152

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_at_origin {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    finiteTimeDimension c t 0 = 0 := by sorry
