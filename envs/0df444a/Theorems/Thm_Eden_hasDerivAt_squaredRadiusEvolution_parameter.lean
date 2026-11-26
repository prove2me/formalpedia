-- Prove2me | Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_parameter
-- name    : Eden.hasDerivAt_squaredRadiusEvolution_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:49.88187+00:00
-- url     : https://prove2.me/theorems/fd427bec-9df0-5026-9176-89403e96b2f3
-- title:
--   Eden: has Deriv At squared Radius Evolution parameter
-- statement:
--   The Eden construction uses the has Deriv At squared Radius Evolution parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L26-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L26-L40

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.hasDerivAt_squaredRadiusEvolution_parameter {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (squaredRadiusEvolution t)
      (Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3) s := by sorry
