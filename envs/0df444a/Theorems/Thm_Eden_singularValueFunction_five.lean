-- Prove2me | Theorems.Thm_Eden_singularValueFunction_five
-- name    : Eden.singularValueFunction_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:56.765352+00:00
-- url     : https://prove2.me/theorems/d8015cfb-46a2-5d10-8162-3ee604b8a76d
-- title:
--   Eden: singular Value Function five
-- statement:
--   The Eden construction uses the singular Value Function five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L105-L111
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L105-L111

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_five (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction A 5 = |A.det| := by sorry
