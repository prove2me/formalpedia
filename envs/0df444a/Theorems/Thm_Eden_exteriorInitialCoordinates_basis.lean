-- Prove2me | Theorems.Thm_Eden_exteriorInitialCoordinates_basis
-- name    : Eden.exteriorInitialCoordinates_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:29.39369+00:00
-- url     : https://prove2.me/theorems/0eccf8bc-6e90-4101-b3e8-124dc99ebce4
-- title:
--   Eden: exterior Initial Coordinates basis
-- statement:
--   The Eden construction uses the exterior Initial Coordinates basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L60-L68
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L60-L68

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

theorem Eden.exteriorInitialCoordinates_basis (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorInitialCoordinates k p (initialExteriorBasisVector k p s) =
      (exteriorBasis k).repr (exteriorBasis k s) := by sorry
