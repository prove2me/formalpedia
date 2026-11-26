-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_attractor_isGreatest
-- name    : Eden.finiteTimeDimension_attractor_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:58.668179+00:00
-- url     : https://prove2.me/theorems/c277b646-bd13-4c7c-a69c-19f54132aad3
-- title:
--   Eden: finite Time Dimension attractor is Greatest
-- statement:
--   The Eden construction uses the finite Time Dimension attractor is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L102-L109
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L102-L109

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_attractor_isGreatest {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) := by sorry
