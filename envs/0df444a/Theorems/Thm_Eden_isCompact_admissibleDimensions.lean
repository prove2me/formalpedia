-- Prove2me | Theorems.Thm_Eden_isCompact_admissibleDimensions
-- name    : Eden.isCompact_admissibleDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:09.851307+00:00
-- url     : https://prove2.me/theorems/10e307e4-1b22-5a97-82cd-5b1995236036
-- title:
--   Eden: is Compact admissible Dimensions
-- statement:
--   The Eden construction uses the is Compact admissible Dimensions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L130-L132
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L130-L132

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.isCompact_admissibleDimensions {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsCompact (admissibleDimensions A) := by sorry
