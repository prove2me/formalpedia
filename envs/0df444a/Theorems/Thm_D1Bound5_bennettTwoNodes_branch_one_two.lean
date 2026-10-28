-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoNodes_branch_one_two
-- name    : D1Bound5.bennettTwoNodes_branch_one_two
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:29:50.159629+00:00
-- url     : https://prove2.me/theorems/efa42c17-dc32-4040-8923-87398f87c4e0
-- title:
--   Bennett Two Nodes branch one two
-- statement:
--   The two nonzero interpolation columns have exactly the root branches used in the tuple-root comparison.
-- source:
--   D1Bound5/BennettRootApproximation.lean, lines 119-135, SHA-256 ca1061aebc87736a011fd6e5cb0011ac939b7397422bdbe21a20c1861b490805. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.bennettTwoNodes_branch_one_two (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (1 + bennettTwoNodes a b 1 * (a * b * c)⁻¹) ^ (1 / 2 : ℂ) =
        (1 + 1 / (a * c)) ^ (1 / 2 : ℂ) ∧
    (1 + bennettTwoNodes a b 2 * (a * b * c)⁻¹) ^ (1 / 2 : ℂ) =
        (1 + 1 / (b * c)) ^ (1 / 2 : ℂ) := by sorry

end D1Bound5
end
