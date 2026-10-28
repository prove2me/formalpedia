-- Prove2me | Theorems.Thm_D1Bound5_finiteM_bennett_identity
-- name    : D1Bound5.finiteM_bennett_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:44.015549+00:00
-- url     : https://prove2.me/theorems/30936d81-b4a0-446f-89ca-45f113745e8b
-- title:
--   Finite M bennett identity
-- statement:
--   Exact comparison with the actual arbitrary-order residue construction. All row and root-column divisions are accounted for by integer polynomials; no residue decomposition or formal identity is assumed.
-- source:
--   D1Bound5/FiniteMBennettIdentity.lean, lines 50-104, SHA-256 291fd6ba981541548cef4bed5210986ea71cc1c1e28ff467e85be78d671f7779. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]











set_option maxHeartbeats 6000000 in
set_option maxRecDepth 4096 in

theorem _root_.D1Bound5.finiteM_bennett_identity (a b s c : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (i j : Fin 4) :
    finiteMBennettEntry a b s c i j =
      finiteMRowFactor a b s i * finiteMMatrix a b s c i j := by sorry





end D1Bound5
end
