-- Prove2me | Theorems.Thm_Eden_supremum_asymptoticDimension_periodic
-- name    : Eden.supremum_asymptoticDimension_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:56.66112+00:00
-- url     : https://prove2.me/theorems/86194918-4740-4382-a1da-a8e3d8e9ff47
-- title:
--   Eden: supremum asymptotic Dimension periodic
-- statement:
--   The Eden construction uses the supremum asymptotic Dimension periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L39-L41
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L39-L41

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremum_asymptoticDimension_periodic {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) = 3 := by sorry
