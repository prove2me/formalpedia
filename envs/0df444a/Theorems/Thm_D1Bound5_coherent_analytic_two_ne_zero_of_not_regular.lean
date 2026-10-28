-- Prove2me | Theorems.Thm_D1Bound5_coherent_analytic_two_ne_zero_of_not_regular
-- name    : D1Bound5.coherent_analytic_two_ne_zero_of_not_regular
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:36.352651+00:00
-- url     : https://prove2.me/theorems/fcfc36b8-1957-4af0-9226-78fdab0a706a
-- title:
--   Coherent analytic two ne zero of not regular
-- statement:
--   The actual analytic coherent form is nonzero whenever the regular-quadruple equation fails. All of its square identities are derived from the branch-fixed analytic construction.
-- source:
--   D1Bound5/CoherentTwoVanishing.lean, lines 25-42, SHA-256 3b9611037cfb35deff1d19449ec5b783d2b2588efa17cbfa510be1c3878acd11. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.coherent_analytic_two_ne_zero_of_not_regular
    (a b p q eta : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hab : a ≠ b)
    (heta : eta ^ 2 = p * q)
    (hreg : (a + b - p - q) ^ 2 ≠ 4 * (a * b + 1) * (p * q + 1)) :
    coherentAnchorRoot a p q eta - coherentAnchorRoot b p q eta -
      (a - b) * coherentTerminalRoot p q eta ≠ 0 := by sorry

end D1Bound5
end
