-- Prove2me | Theorems.Thm_Eden_singularWeight_eq_fraction
-- name    : Eden.singularWeight_eq_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:23.117565+00:00
-- url     : https://prove2.me/theorems/1ddab90d-f2f7-5963-8b51-f7f44e24c584
-- title:
--   Eden: singular Weight eq fraction
-- statement:
--   The Eden construction uses the singular Weight eq fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L34-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L34-L36

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularWeight_eq_fraction (k : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    singularWeight k ((k : ℝ) + α) = α := by sorry
