-- Prove2me | Theorems.Thm_Eden_hasDerivAt_evolution
-- name    : Eden.hasDerivAt_evolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:03:20.525099+00:00
-- url     : https://prove2.me/theorems/089a55a3-eb3a-5e83-b5a6-3d5074b23ad9
-- title:
--   Eden: has Deriv At evolution
-- statement:
--   The explicit evolution satisfies the Cartesian vector field.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L41-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L41-L55

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by sorry
