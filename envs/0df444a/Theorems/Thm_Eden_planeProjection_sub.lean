-- Prove2me | Theorems.Thm_Eden_planeProjection_sub
-- name    : Eden.planeProjection_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:25:39.420163+00:00
-- url     : https://prove2.me/theorems/efab4d27-b1d7-544e-8fd4-af3b2cedc967
-- title:
--   Eden: plane Projection sub
-- statement:
--   The Eden construction uses the plane Projection sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L37-L39
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L37-L39

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.planeProjection_sub (j : Fin 2) (p q : PhaseSpace) :
    planeProjection j (p - q) = planeProjection j p - planeProjection j q := by sorry
