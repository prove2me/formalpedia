-- Prove2me | Theorems.Thm_Eden_forwardOrbit_eq_secondCircle
-- name    : Eden.forwardOrbit_eq_secondCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:56.012565+00:00
-- url     : https://prove2.me/theorems/7dd4ca76-72f6-4da0-8fc4-72476c9b6654
-- title:
--   Eden: forward Orbit eq second Circle
-- statement:
--   The second-plane circles are also whole geometric orbits, at frequency sqrt(2).
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L110-L123
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L110-L123

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.forwardOrbit_eq_secondCircle (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ secondCircle s) : forwardOrbit c p = secondCircle s := by sorry
