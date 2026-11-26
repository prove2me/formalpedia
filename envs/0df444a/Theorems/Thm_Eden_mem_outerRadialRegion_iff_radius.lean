-- Prove2me | Theorems.Thm_Eden_mem_outerRadialRegion_iff_radius
-- name    : Eden.mem_outerRadialRegion_iff_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:35.187908+00:00
-- url     : https://prove2.me/theorems/f4bcd83d-c159-4134-a3ce-1f73900df413
-- title:
--   Eden: mem outer Radial Region iff radius
-- statement:
--   The Eden construction uses the mem outer Radial Region iff radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L33-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L33-L35

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.mem_outerRadialRegion_iff_radius (p : PhaseSpace) :
    p ∈ outerRadialRegion ↔ p ∈ attractor ∧ 1 < Real.sqrt (radiusSq₁ p) := by sorry
