-- Prove2me | Theorems.Thm_Eden_evolution_unique
-- name    : Eden.evolution_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:28.168304+00:00
-- url     : https://prove2.me/theorems/1548961a-7cc5-5498-a710-db62f1f7967b
-- title:
--   Eden: evolution unique
-- statement:
--   The explicit evolution is the unique global forward solution, allowing the usual
--   right-sided differential equation at time zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L53-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L53-L63

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_unique (c : ℝ) (p : PhaseSpace) {f : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Ici 0))
    (hf' : ∀ t, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t)
    (h0 : f 0 = p) : EqOn f (fun t => evolution c t p) (Ici 0) := by sorry
