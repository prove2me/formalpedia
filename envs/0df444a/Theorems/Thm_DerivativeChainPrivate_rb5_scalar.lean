-- Prove2me | Theorems.Thm_DerivativeChainPrivate_rb5_scalar
-- name    : DerivativeChainPrivate.rb5_scalar
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:55:06.543155+00:00
-- url     : https://prove2.me/theorems/527cdccd-74f0-44fc-a109-dfae7730a587
-- title:
--   RB5 scalar optimization under the disk variance constraint
-- statement:
--   For real N,c,u,V with 0 <= c < N, V >= 0 and u^2+V <= 1, the expression 1+sqrt(u^2+cV/N)+c sqrt(V/N) is at most 1+sqrt(1+c^2/(N-c)). This is a scalar inequality, not the polynomial RB5 theorem.
-- source:
--   Derivative-zero chains: public formalization reference, R33, DerivativeChainPrivate.rb5_scalar. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.rb5_scalar (N c u V : ℝ) (hc : 0 ≤ c) (hNc : c < N)
    (hV : 0 ≤ V) (huV : u ^ 2 + V ≤ 1) :
    1 + Real.sqrt (u ^ 2 + c * V / N) + c * Real.sqrt (V / N) ≤
      1 + Real.sqrt (1 + c ^ 2 / (N - c)) := by sorry
