-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_parameter_rows
-- name    : D1Bound5.coherent_three_parameter_rows
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:39:03.237188+00:00
-- url     : https://prove2.me/theorems/155c5b91-7993-4b21-aeb0-c830cac27d5a
-- title:
--   Coherent three parameter rows
-- statement:
--   All exact rational comparisons for the manuscript's two rows.
-- source:
--   D1Bound5/CoherentThreeParameters.lean, lines 152-162, SHA-256 ca0fac013bc4ef76939f023e46143eabcee36be640a6d47b13f0373264757949. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions

section
open Finset

noncomputable section

namespace D1Bound5
















theorem _root_.D1Bound5.coherent_three_parameter_rows :
    (0 < coherentThreeLowerConstant 32 ∧
      100*coherentThreeUpperConstant 32/99 < (1/10 : ℝ) ∧
      5 < 100/(201*coherentThreeUpperConstant 32) ∧
      100/(199*coherentThreeLowerConstant 32) < 179/10) ∧
    (0 < coherentThreeLowerConstant 48 ∧
      100*coherentThreeUpperConstant 48/99 < (19/200 : ℝ) ∧
      5 < 100/(201*coherentThreeUpperConstant 48) ∧
      100/(199*coherentThreeLowerConstant 48) < 15) := by sorry

end D1Bound5
end
