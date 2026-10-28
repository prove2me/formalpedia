-- Prove2me | Theorems.Thm_D1Bound5_pellFiniteCertificate_exists
-- name    : D1Bound5.pellFiniteCertificate_exists
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:15.917+00:00
-- url     : https://prove2.me/theorems/45a2590d-8e06-40fb-a833-d0e57e33fa34
-- title:
--   Pell Finite Certificate exists
-- statement:
--   All 1016 eligible parameters have complete, kernel-checked certificates. The excluded cases have explicit nonunit square divisors, so the coverage proof does not trust the Python squarefree predicate.
-- source:
--   D1Bound5/PellFiniteFields.lean, lines 91-110, SHA-256 352c30df17c6d6e5a3b765a23814fee880412e130767d7c10f6bf24c2c1ef96d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000












theorem _root_.D1Bound5.pellFiniteCertificate_exists (d : ℤ) (hd : 7 ≤ d) (hupper : d < 10000)
    (hmod : d % 8 = 7) (hsq : Squarefree d) :
    Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
