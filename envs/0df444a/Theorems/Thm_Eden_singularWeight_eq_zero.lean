-- Prove2me | Theorems.Thm_Eden_singularWeight_eq_zero
-- name    : Eden.singularWeight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:00.687839+00:00
-- url     : https://prove2.me/theorems/7afebf18-8a06-493a-8b1d-8324fbca4953
-- title:
--   Eden: singular Weight eq zero
-- statement:
--   The Eden construction uses the singular Weight eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L38-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L38-L43

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularWeight_eq_zero {i k : ℕ} (hki : k < i) {α : ℝ} (hα : α ≤ 1) :
    singularWeight i ((k : ℝ) + α) = 0 := by sorry
