-- Prove2me | Theorems.Thm_Eden_firstCircle_invariant
-- name    : Eden.firstCircle_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:27.644247+00:00
-- url     : https://prove2.me/theorems/bc900d2f-bdd8-44b9-9903-137a5f8278a9
-- title:
--   Eden: first Circle invariant
-- statement:
--   The Eden construction uses the first Circle invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L73-L81
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean#L73-L81

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.firstCircle_invariant (c : ℝ) {s t : ℝ} (hs : s = 1 ∨ s = 2)
    (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ firstCircle s) :
    evolution c t p ∈ firstCircle s := by sorry
