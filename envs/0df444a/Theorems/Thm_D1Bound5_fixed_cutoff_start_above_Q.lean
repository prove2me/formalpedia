-- Prove2me | Theorems.Thm_D1Bound5_fixed_cutoff_start_above_Q
-- name    : D1Bound5.fixed_cutoff_start_above_Q
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:30.264489+00:00
-- url     : https://prove2.me/theorems/2ccf804a-f113-4132-a520-7c51f606e719
-- title:
--   Fixed cutoff start above Q
-- statement:
--   Scalar conversion of the first overlap, retaining every strict inequality. The two growth premises are precisely the actual retained bounds already proved for fixed triples.
-- source:
--   D1Bound5/OneSmallCutoffReal.lean, lines 43-74, SHA-256 cfc21933cb4a82de4a9d5409cd9e6c6bc2d0d33f2b3a2f409c936a0b91b57d93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
namespace D1Bound5






theorem _root_.D1Bound5.fixed_cutoff_start_above_Q (K S T C D : ℝ)
    (hK : 0 < K) (hS : 0 < S) (hT : 0 < T) (hC : 0 < C)
    (hgap : K*T^5/S^2 < C) (hstart : C^7/(S^2*T^4) < D)
    (hover : 1 < (1-1/4000 : ℝ)*K^4*T^10/(12100*S^10)) :
    4*55^2*T^6*C^3/(1-1/4000 : ℝ) < D := by sorry

end D1Bound5
end
