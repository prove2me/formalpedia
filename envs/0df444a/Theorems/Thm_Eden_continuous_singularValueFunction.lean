-- Prove2me | Theorems.Thm_Eden_continuous_singularValueFunction
-- name    : Eden.continuous_singularValueFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:59.489845+00:00
-- url     : https://prove2.me/theorems/f4e0c474-d404-466a-87c0-e9edbe74bb2b
-- title:
--   Eden: continuous singular Value Function
-- statement:
--   The Eden construction uses the continuous singular Value Function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L113-L119
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L113-L119

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuous_singularValueFunction {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : Continuous (singularValueFunction A) := by sorry
