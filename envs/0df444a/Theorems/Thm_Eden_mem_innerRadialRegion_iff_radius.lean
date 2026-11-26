-- Prove2me | Theorems.Thm_Eden_mem_innerRadialRegion_iff_radius
-- name    : Eden.mem_innerRadialRegion_iff_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:49.207488+00:00
-- url     : https://prove2.me/theorems/cbcca72b-e3bd-41c2-b852-65f5d899bb4a
-- title:
--   Eden: mem inner Radial Region iff radius
-- statement:
--   The Eden construction uses the mem inner Radial Region iff radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L29-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L29-L31

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.mem_innerRadialRegion_iff_radius (p : PhaseSpace) :
    p ∈ innerRadialRegion ↔ p ∈ attractor ∧ Real.sqrt (radiusSq₁ p) < 1 := by sorry
