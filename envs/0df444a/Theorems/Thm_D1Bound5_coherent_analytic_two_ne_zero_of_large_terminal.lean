-- Prove2me | Theorems.Thm_D1Bound5_coherent_analytic_two_ne_zero_of_large_terminal
-- name    : D1Bound5.coherent_analytic_two_ne_zero_of_large_terminal
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:46.394404+00:00
-- url     : https://prove2.me/theorems/82a617ea-ebbe-4d7a-88bc-dbdefbcfe346
-- title:
--   Coherent analytic two ne zero of large terminal
-- statement:
--   The manuscript's actual large-terminal size hypothesis forces the two-anchor coherent form nonzero, with no nonvanishing premise.
-- source:
--   D1Bound5/CoherentTwoSize.lean, lines 131-146, SHA-256 8a8f6db3352296dc34c3bf72970d3d3c0c58939fc28136095cce2e2e458acdfa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
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
open Finset
open scoped NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.coherent_analytic_two_ne_zero_of_large_terminal
    (a b p q eta r s t : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hab : a ≠ b)
    (heta : eta ^ 2 = p * q)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * p + 1)
    (ht : t ^ 2 = b * p + 1)
    (hA : 1 ≤ ‖a‖) (hB : 3 ≤ ‖b‖) (hP : 5 * ‖b‖ ≤ ‖p‖)
    (hQ : 5 * ‖a‖ * ‖b‖ * ‖p‖ ≤ ‖q‖) :
    coherentAnchorRoot a p q eta - coherentAnchorRoot b p q eta -
      (a - b) * coherentTerminalRoot p q eta ≠ 0 := by sorry



end D1Bound5
end
