-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_attractor_isGreatest
-- name    : Eden.asymptoticDimension_attractor_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:01.032523+00:00
-- url     : https://prove2.me/theorems/298271d6-9b36-49ed-96a9-93e2107a95d1
-- title:
--   Eden: asymptotic Dimension attractor is Greatest
-- statement:
--   The Eden construction uses the asymptotic Dimension attractor is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L137-L143
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L137-L143

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.asymptoticDimension_attractor_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' attractor) (targetDimension c) := by sorry
