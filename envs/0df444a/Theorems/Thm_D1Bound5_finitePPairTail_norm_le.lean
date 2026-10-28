-- Prove2me | Theorems.Thm_D1Bound5_finitePPairTail_norm_le
-- name    : D1Bound5.finitePPairTail_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:44.913783+00:00
-- url     : https://prove2.me/theorems/854b57ad-c6fe-4fed-b1fb-391883295001
-- title:
--   Finite PPair Tail norm le
-- statement:
--   Actual Taylor tails for the two pair-row types, with the exact finite absolute-coefficient totals876 and2676.
-- source:
--   D1Bound5/FinitePTailBound.lean, lines 56-78, SHA-256 ab0bc04a98f79bcb424f4bb78f9ebf8d6779a1a1bf51c7bd6e2f84df375808ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.finitePPairTail_norm_le (u v c : ℂ) (A S : ℝ)
    (hA1 : 1 ≤ A) (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huS : ‖u‖ ≤ S) (hvS : ‖v‖ ≤ S) (hAC : 1000 ≤ A*‖c‖) (kind : Fin 2) :
    ‖finitePPairTail u v c kind‖ ≤ (![876,2676] kind : ℕ)*
      ((21/1024 : ℝ)*(1000/999)*S^2/(A^4*‖c‖^6)) := by sorry



end D1Bound5
end
