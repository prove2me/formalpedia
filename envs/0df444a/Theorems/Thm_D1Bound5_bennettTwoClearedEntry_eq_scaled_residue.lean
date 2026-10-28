-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_eq_scaled_residue
-- name    : D1Bound5.bennettTwoClearedEntry_eq_scaled_residue
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:54.366297+00:00
-- url     : https://prove2.me/theorems/cdf4ce33-a9ce-4c11-a62e-51094b319078
-- title:
--   Bennett Two Cleared Entry eq scaled residue
-- statement:
--   Exact identification with the manuscript's clearing factor applied to the original residue coefficient f=P(1/N), with H=ab and N=abc.
-- source:
--   D1Bound5/BennettTwoIntegralEntries.lean, lines 138-151, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


























theorem _root_.D1Bound5.bennettTwoClearedEntry_eq_scaled_residue
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (k : ℕ) (i j : Fin 3) :
    bennettTwoClearedEntry a b c k i j =
      (4 * (a * b) ^ 2 * c * (a - b) ^ 2) ^ k *
        (bennettPolynomialResidue Finset.univ (bennettTwoNodes a b) k (1 / 2 : F)
          i j).eval ((a * b * c)⁻¹) := by sorry



end D1Bound5
end
