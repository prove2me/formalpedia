-- Prove2me | Theorems.Thm_Eden_admissibleDimensions_nonempty
-- name    : Eden.admissibleDimensions_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:27.268872+00:00
-- url     : https://prove2.me/theorems/93204f12-bca3-443d-9d38-b9bf1375aca1
-- title:
--   Eden: admissible Dimensions nonempty
-- statement:
--   The Eden construction uses the admissible Dimensions nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L125-L128
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L125-L128

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.admissibleDimensions_nonempty (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    (admissibleDimensions A).Nonempty := by sorry
