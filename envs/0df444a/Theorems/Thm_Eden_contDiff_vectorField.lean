-- Prove2me | Theorems.Thm_Eden_contDiff_vectorField
-- name    : Eden.contDiff_vectorField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:22.169203+00:00
-- url     : https://prove2.me/theorems/6f5660e5-8168-46dd-9a2d-8bb0f6ea5f16
-- title:
--   Eden: cont Diff vector Field
-- statement:
--   Polynomial smoothness of the vector field, at every differentiability order.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L66-L69
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean#L66-L69

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiff_vectorField (c : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (vectorField c) := by sorry
