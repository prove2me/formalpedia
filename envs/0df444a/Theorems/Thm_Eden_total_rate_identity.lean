-- Prove2me | Theorems.Thm_Eden_total_rate_identity
-- name    : Eden.total_rate_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:47.25095+00:00
-- url     : https://prove2.me/theorems/338ed9dd-89f4-535e-a4a1-4d1f2922da31
-- title:
--   Eden: total rate identity
-- statement:
--   Algebraic sum of the five variational rates.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L68-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L68-L72

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.total_rate_identity (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c =
      4 - c - 6 * (s₁ - 1) ^ 2 - 6 * (s₂ - 1) ^ 2 := by sorry
