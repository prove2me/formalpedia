-- Prove2me | Theorems.Thm_Eden_supremum_finiteTimeDimension_attractor
-- name    : Eden.supremum_finiteTimeDimension_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:49.300036+00:00
-- url     : https://prove2.me/theorems/4c5df954-dffd-591a-9a8c-b97df15b362d
-- title:
--   Eden: supremum finite Time Dimension attractor
-- statement:
--   The Eden construction uses the supremum finite Time Dimension attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L111-L113
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L111-L113

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremum_finiteTimeDimension_attractor {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' attractor) = targetDimension c := by sorry
