-- Prove2me | Theorems.Thm_Eden_continuous_singularWeight
-- name    : Eden.continuous_singularWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:26.597248+00:00
-- url     : https://prove2.me/theorems/7869ea9a-8be5-481f-b072-5b02e0e8495e
-- title:
--   Eden: continuous singular Weight
-- statement:
--   The Eden construction uses the continuous singular Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L24-L26
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L24-L26

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuous_singularWeight (i : ℕ) : Continuous (singularWeight i) := by sorry
