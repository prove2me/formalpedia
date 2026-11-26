-- Prove2me | Theorems.Thm_Eden_initialExteriorBasisVector_ne_zero
-- name    : Eden.initialExteriorBasisVector_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:34.935295+00:00
-- url     : https://prove2.me/theorems/af363489-80d8-4cdc-a306-789f79da3a08
-- title:
--   Eden: initial Exterior Basis Vector ne zero
-- statement:
--   The Eden construction uses the initial Exterior Basis Vector ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L53-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L53-L58

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.initialExteriorBasisVector_ne_zero (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    initialExteriorBasisVector k p s ≠ 0 := by sorry
