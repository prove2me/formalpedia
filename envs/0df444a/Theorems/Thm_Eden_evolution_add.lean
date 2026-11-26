-- Prove2me | Theorems.Thm_Eden_evolution_add
-- name    : Eden.evolution_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:06:27.04026+00:00
-- url     : https://prove2.me/theorems/18c7c9dc-63d5-44bd-b59e-ece6e36acdaa
-- title:
--   Eden: evolution add
-- statement:
--   The explicit solutions have the semigroup law for every ambient initial point
--   and all nonnegative times.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L67-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L67-L78

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_add (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    evolution c (s + t) p = evolution c t (evolution c s p) := by sorry
