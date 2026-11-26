-- Prove2me | Theorems.Thm_Eden_exists_planar_time_on_stationary_radius
-- name    : Eden.exists_planar_time_on_stationary_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:44.354312+00:00
-- url     : https://prove2.me/theorems/498d1855-6b5c-439e-898a-3bcf583a0119
-- title:
--   Eden: exists planar time on stationary radius
-- statement:
--   The Eden construction uses the exists planar time on stationary radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L57-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L57-L71

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exists_planar_time_on_stationary_radius {Ω s x y u v : ℝ}
    (hΩ : 0 < Ω) (hs : s = 1 ∨ s = 2)
    (hxy : x ^ 2 + y ^ 2 = s) (huv : u ^ 2 + v ^ 2 = s) :
    ∃ t : ℝ, 0 < t ∧ planarX Ω t x y = u ∧ planarY Ω t x y = v := by sorry
