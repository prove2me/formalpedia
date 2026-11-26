-- Prove2me | Theorems.Thm_Eden_frequency_solution_unique_on_Icc
-- name    : Eden.frequency_solution_unique_on_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:27:40.350363+00:00
-- url     : https://prove2.me/theorems/0bc36065-f2d7-5673-93ee-3fbb98eeff59
-- title:
--   Eden: frequency solution unique on Icc
-- statement:
--   Two solution arcs with the same initial value agree on their whole
--   closed time interval. Right derivatives suffice at the initial endpoint.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L23-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L23-L45

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.frequency_solution_unique_on_Icc (c ν : ℝ) {a b : ℝ} {f g : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (frequencyVectorField c ν (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (frequencyVectorField c ν (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by sorry
