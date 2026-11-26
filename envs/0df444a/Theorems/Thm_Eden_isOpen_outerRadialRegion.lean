-- Prove2me | Theorems.Thm_Eden_isOpen_outerRadialRegion
-- name    : Eden.isOpen_outerRadialRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:10.769635+00:00
-- url     : https://prove2.me/theorems/d2bd0915-e374-5d0b-832b-3baf1dc40e9a
-- title:
--   Eden: is Open outer Radial Region
-- statement:
--   The Eden construction uses the is Open outer Radial Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L63-L67
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L63-L67

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.isOpen_outerRadialRegion :
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} := by sorry
