-- Prove2me | Theorems.Thm_Eden_frequencyEvolution_unique
-- name    : Eden.frequencyEvolution_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:55.723568+00:00
-- url     : https://prove2.me/theorems/b38fb4cc-6afe-4bea-993e-8bd9e8329a65
-- title:
--   Eden: frequency Evolution unique
-- statement:
--   The explicit evolution is the unique global forward solution, allowing
--   the usual right-sided differential equation at time zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L53-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L53-L63

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.frequencyEvolution_unique (c ν : ℝ) (p : PhaseSpace) {f : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Ici 0))
    (hf' : ∀ t, 0 ≤ t → HasDerivWithinAt f (frequencyVectorField c ν (f t)) (Ici t) t)
    (h0 : f 0 = p) : EqOn f (fun t => frequencyEvolution c ν t p) (Ici 0) := by sorry
