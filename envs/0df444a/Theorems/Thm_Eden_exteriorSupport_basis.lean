-- Prove2me | Theorems.Thm_Eden_exteriorSupport_basis
-- name    : Eden.exteriorSupport_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:00.11086+00:00
-- url     : https://prove2.me/theorems/9ad4c986-56ca-5095-bd9a-81e98af24996
-- title:
--   Eden: exterior Support basis
-- statement:
--   The Eden construction uses the exterior Support basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L70-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L70-L74

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

theorem Eden.exteriorSupport_basis (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorSupport k p (initialExteriorBasisVector k p s) = {s} := by sorry
