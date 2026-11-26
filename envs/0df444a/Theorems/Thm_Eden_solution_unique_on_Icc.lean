-- Prove2me | Theorems.Thm_Eden_solution_unique_on_Icc
-- name    : Eden.solution_unique_on_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:04:14.236531+00:00
-- url     : https://prove2.me/theorems/721e6c0e-800e-5039-97cf-608822d111bb
-- title:
--   Eden: solution unique on Icc
-- statement:
--   Two solution arcs with the same initial value agree on their whole closed time
--   interval. Right derivatives suffice at the initial endpoint.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L23-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L23-L45

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.solution_unique_on_Icc (c : ℝ) {a b : ℝ} {f g : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (vectorField c (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (vectorField c (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by sorry
