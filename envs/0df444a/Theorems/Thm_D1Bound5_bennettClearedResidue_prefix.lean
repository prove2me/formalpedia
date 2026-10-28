-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedResidue_prefix
-- name    : D1Bound5.bennettClearedResidue_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:27.35503+00:00
-- url     : https://prove2.me/theorems/0af90046-1e37-4c7b-832b-1dc7ab4ae34b
-- title:
--   Bennett Cleared Residue prefix
-- statement:
--   Removing the final node gives exactly the cleared residue construction on the prefix, including the distinguished row multiplicity.
-- source:
--   D1Bound5/BennettNodeRemoval.lean, lines 28-39, SHA-256 744b0d9ca6cef7f147ff8e1fb3ed54499f22a4c9c12ff289d69e5603296721b1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennettClearedResidue_prefix (n : ℕ) (a : Fin (n + 1) → F)
    (k : ℕ) (ν : F) (i j : Fin n) :
    bennettClearedResidue (Finset.univ.erase (Fin.last n)) a k ν i.castSucc j.castSucc =
      bennettClearedResidue Finset.univ (fun l : Fin n ↦ a l.castSucc) k ν i j := by sorry



end D1Bound5
end
