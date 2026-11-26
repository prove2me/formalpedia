-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_mem_interval
-- name    : Eden.finiteTimeDimension_mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:49.741719+00:00
-- url     : https://prove2.me/theorems/80906576-a9b3-5cad-b2a2-d99c7d35f967
-- title:
--   Eden: finite Time Dimension mem interval
-- statement:
--   The Eden construction uses the finite Time Dimension mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L151-L152
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L151-L152

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_mem_interval (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    finiteTimeDimension c t p ∈ Icc 0 5 := by sorry
