-- Prove2me | Theorems.Thm_Eden_exists_global_forward_solution
-- name    : Eden.exists_global_forward_solution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:06:35.708629+00:00
-- url     : https://prove2.me/theorems/6b75de25-e1de-4fff-aa4a-fcf5fe342a49
-- title:
--   Eden: exists global forward solution
-- statement:
--   A global forward solution exists through every point of the ambient space.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L59-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L59-L63

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exists_global_forward_solution (c : ℝ) (p : PhaseSpace) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t := by sorry
