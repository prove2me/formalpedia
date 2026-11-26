-- Prove2me | Theorems.Thm_Eden_supremum_commonIndexLocalDimension_periodic
-- name    : Eden.supremum_commonIndexLocalDimension_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:17.865347+00:00
-- url     : https://prove2.me/theorems/3d5d85ef-483b-5470-a7bc-7432ab8ea8d0
-- title:
--   Eden: supremum common Index Local Dimension periodic
-- statement:
--   The Eden construction uses the supremum common Index Local Dimension periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L90-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L90-L92

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremum_commonIndexLocalDimension_periodic {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) = 4 - 2 / c := by sorry
