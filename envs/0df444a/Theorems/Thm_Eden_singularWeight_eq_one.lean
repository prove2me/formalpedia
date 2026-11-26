-- Prove2me | Theorems.Thm_Eden_singularWeight_eq_one
-- name    : Eden.singularWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:45.708484+00:00
-- url     : https://prove2.me/theorems/5e6b6064-0702-4ee0-a4d2-7ace79ff1b96
-- title:
--   Eden: singular Weight eq one
-- statement:
--   The Eden construction uses the singular Weight eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L28-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L28-L32

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularWeight_eq_one {i k : ℕ} (hik : i < k) {α : ℝ} (hα : 0 ≤ α) :
    singularWeight i ((k : ℝ) + α) = 1 := by sorry
