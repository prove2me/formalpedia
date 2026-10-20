-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_prefix_scalar
-- name    : DerivativeChainPrivate.cubic_prefix_scalar
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:57:05.052988+00:00
-- url     : https://prove2.me/theorems/3ac1c6c3-dc69-43f8-bd18-e97a583b1a7a
-- title:
--   The one-pair cubic prefix squared-cost inequality
-- statement:
--   For all real x and b, (b+sqrt(x^2+b^2))^2 <= 2(x^2+2b^2). This is the scalar estimate from the one-pair argument; it does not establish cubic root locations or variance contraction.
-- source:
--   Derivative-zero chains: public formalization reference, R36, DerivativeChainPrivate.cubic_prefix_scalar. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.cubic_prefix_scalar (x b : ℝ) :
    (b + Real.sqrt (x ^ 2 + b ^ 2)) ^ 2 ≤ 2 * (x ^ 2 + 2 * b ^ 2) := by sorry
