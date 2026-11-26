-- Prove2me | Theorems.Thm_Eden_continuous_radialDiscriminant_time
-- name    : Eden.continuous_radialDiscriminant_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:53.321504+00:00
-- url     : https://prove2.me/theorems/9b9e60d5-4949-5a60-aafd-2181e83cb78e
-- title:
--   Eden: continuous radial Discriminant time
-- statement:
--   The Eden construction uses the continuous radial Discriminant time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L42-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L42-L45

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.continuous_radialDiscriminant_time (s : ℝ) :
    Continuous (fun t => radialDiscriminant t s) := by sorry
