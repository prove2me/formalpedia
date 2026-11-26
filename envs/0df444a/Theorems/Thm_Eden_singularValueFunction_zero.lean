-- Prove2me | Theorems.Thm_Eden_singularValueFunction_zero
-- name    : Eden.singularValueFunction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:41.822949+00:00
-- url     : https://prove2.me/theorems/48b0a191-4726-50f8-8b81-9d6f2f470972
-- title:
--   Eden: singular Value Function zero
-- statement:
--   The Eden construction uses the singular Value Function zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L96-L97
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L96-L97

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_zero (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction A 0 = 1 := by sorry
