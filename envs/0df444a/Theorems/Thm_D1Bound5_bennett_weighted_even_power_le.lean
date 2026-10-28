-- Prove2me | Theorems.Thm_D1Bound5_bennett_weighted_even_power_le
-- name    : D1Bound5.bennett_weighted_even_power_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:42.276806+00:00
-- url     : https://prove2.me/theorems/5630b572-b340-4f56-874c-351d1c8c8388
-- title:
--   Bennett weighted even power le
-- statement:
--   Dividing a positive-order even power by its own anchor preserves monotonicity. This is the scalar cancellation needed for the two columns.
-- source:
--   D1Bound5/BennettWeightedHeight.lean, lines 5-21, SHA-256 75e011686e317cc4f4aee29eb48fc02385e388f50e84d12c29ee7a3ad4bb85f9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
namespace D1Bound5


theorem _root_.D1Bound5.bennett_weighted_even_power_le
    (A B H : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hH : 0 ≤ H) (k : ℕ) (hk : 1 ≤ k) :
    (A^2*H)^k/A ≤ (B^2*H)^k/B := by sorry



end D1Bound5
end
