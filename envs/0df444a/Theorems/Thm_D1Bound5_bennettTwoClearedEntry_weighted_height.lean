-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_weighted_height
-- name    : D1Bound5.bennettTwoClearedEntry_weighted_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:33.376862+00:00
-- url     : https://prove2.me/theorems/4a8dccf6-4836-495c-8380-53f5bd71e98c
-- title:
--   Bennett Two Cleared Entry weighted height
-- statement:
--   The actual two anchor columns satisfy the combined height bound used in the integral approximation form, with no coefficient bound premise.
-- source:
--   D1Bound5/BennettWeightedHeight.lean, lines 23-48, SHA-256 75e011686e317cc4f4aee29eb48fc02385e388f50e84d12c29ee7a3ad4bb85f9. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoClearedEntry_weighted_height
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoClearedEntry a b c k i 1‖/‖a‖ +
        ‖bennettTwoClearedEntry a b c k i 2‖/‖b‖ <
      2*(42*‖b‖^3*‖c‖)^k/‖b‖ := by sorry

end D1Bound5
end
