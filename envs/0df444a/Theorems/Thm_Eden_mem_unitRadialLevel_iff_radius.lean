-- Prove2me | Theorems.Thm_Eden_mem_unitRadialLevel_iff_radius
-- name    : Eden.mem_unitRadialLevel_iff_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:27.667845+00:00
-- url     : https://prove2.me/theorems/4dd43237-82af-5b1a-99d9-17a55fa2ebc2
-- title:
--   Eden: mem unit Radial Level iff radius
-- statement:
--   The Eden construction uses the mem unit Radial Level iff radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L37-L39
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L37-L39

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.mem_unitRadialLevel_iff_radius (p : PhaseSpace) :
    p ∈ unitRadialLevel ↔ p ∈ attractor ∧ Real.sqrt (radiusSq₁ p) = 1 := by sorry
