-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_lt_target_of_not_mem_torus
-- name    : Eden.asymptoticDimension_lt_target_of_not_mem_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:40.986862+00:00
-- url     : https://prove2.me/theorems/b9d79744-1895-5371-8367-f22b1cd0c0cb
-- title:
--   Eden: asymptotic Dimension lt target of not mem torus
-- statement:
--   The Eden construction uses the asymptotic Dimension lt target of not mem torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L127-L131
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L127-L131

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.asymptoticDimension_lt_target_of_not_mem_torus {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    asymptoticDimension c p < targetDimension c := by sorry
