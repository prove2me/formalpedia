-- Prove2me | Theorems.Thm_D1Bound5_tail_irregular_of_four_le
-- name    : D1Bound5.tail_irregular_of_four_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:55.01499+00:00
-- url     : https://prove2.me/theorems/c8755fd5-e4d5-44c3-aa38-3d64937db487
-- title:
--   Tail irregular of four le
-- statement:
--   The C>=4 branch of lem:tail-irregular in the full ring of integers of every imaginary quadratic field. No root is assumed to be nonzero.
-- source:
--   D1Bound5/TailAnalyticMain.lean, lines 151-178, SHA-256 ecaba9e1e964c7e6c51088002aaaf592031aa2393ee6eb52d94273cfda86b389. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.tail_irregular_of_four_le {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c d : 𝓞 K) (ha : a ≠ 0)
    (hab : ∃ u : 𝓞 K, u^2 = a*b+1) (hac : ∃ v : 𝓞 K, v^2 = a*c+1)
    (had : ∃ w : 𝓞 K, w^2 = a*d+1) (hbc : ∃ r : 𝓞 K, r^2 = b*c+1)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖) (hB : 3 ≤ ‖phi (b : K)‖)
    (hC : 4 ≤ ‖phi (c : K)‖) (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖) :
    regularDefect b c d ≠ 0 := by sorry




end D1Bound5
end
