-- Prove2me | Theorems.Thm_Eden_attractor_not_subset_closure_forwardOrbit
-- name    : Eden.attractor_not_subset_closure_forwardOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:21.553264+00:00
-- url     : https://prove2.me/theorems/bbbfd9d6-8ddb-4f3e-99c9-68d60219c67f
-- title:
--   Eden: attractor not subset closure forward Orbit
-- statement:
--   No forward orbit can have the whole attractor in its closure. The statement also
--   permits ambient initial points outside A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L114-L131
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L114-L131

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.attractor_not_subset_closure_forwardOrbit (c : ℝ) (p : PhaseSpace) :
    ¬ attractor ⊆ closure (forwardOrbit c p) := by sorry
