-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_le_target
-- name    : Eden.asymptoticDimension_le_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:23.720526+00:00
-- url     : https://prove2.me/theorems/7bce81e2-a9ff-40e3-8eda-fc05ec33ab14
-- title:
--   Eden: asymptotic Dimension le target
-- statement:
--   The Eden construction uses the asymptotic Dimension le target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L105-L109
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L105-L109

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.asymptoticDimension_le_target {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p ≤ targetDimension c := by sorry
