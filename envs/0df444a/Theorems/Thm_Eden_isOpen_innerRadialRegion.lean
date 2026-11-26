-- Prove2me | Theorems.Thm_Eden_isOpen_innerRadialRegion
-- name    : Eden.isOpen_innerRadialRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:40.599986+00:00
-- url     : https://prove2.me/theorems/38ca3d10-3a64-525f-9762-b05fe4a5b33a
-- title:
--   Eden: is Open inner Radial Region
-- statement:
--   Openness is in the subspace topology of the attractor.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L57-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L57-L61

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.isOpen_innerRadialRegion :
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} := by sorry
