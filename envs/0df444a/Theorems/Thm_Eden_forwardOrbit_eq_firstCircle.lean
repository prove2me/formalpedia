-- Prove2me | Theorems.Thm_Eden_forwardOrbit_eq_firstCircle
-- name    : Eden.forwardOrbit_eq_firstCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:46.765615+00:00
-- url     : https://prove2.me/theorems/08639c07-f158-53b8-b8e0-708876851468
-- title:
--   Eden: forward Orbit eq first Circle
-- statement:
--   Every point of a invariant circle has that entire circle as its geometric orbit.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L94-L107
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L94-L107

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.forwardOrbit_eq_firstCircle (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s) : forwardOrbit c p = firstCircle s := by sorry
