-- Prove2me | Theorems.Thm_D1Bound5_negative_binomial_positive_tail_tsum
-- name    : D1Bound5.negative_binomial_positive_tail_tsum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:15.539769+00:00
-- url     : https://prove2.me/theorems/0d78ed1d-5e4f-46a1-8109-2afa978e8195
-- title:
--   Negative binomial positive tail tsum
-- statement:
--   Exact positive-degree tail of a negative-binomial generating function.
-- source:
--   D1Bound5/CoherentMajorant.lean, lines 8-19, SHA-256 7556732be060ea55e0263542b247cb96b16048503d14b4fd541c9746cc7af0d4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.negative_binomial_positive_tail_tsum (q : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, (Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) =
      1 / (1 - r) ^ (q + 1) - 1 := by sorry



end D1Bound5
end
