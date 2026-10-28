-- Prove2me | Theorems.Thm_D1Bound5_coherentVandermonde4_norm_le
-- name    : D1Bound5.coherentVandermonde4_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:11.140416+00:00
-- url     : https://prove2.me/theorems/4d36a270-1018-489c-a29a-661c4ee9318d
-- title:
--   Coherent Vandermonde4 norm le
-- statement:
--   The exact 24-monomial expansion of the four-anchor Vandermonde has the sorted modulus bound used in the direct-four estimate.
-- source:
--   D1Bound5/CoherentVandermondeFourNorm.lean, lines 8-53, SHA-256 f0df55ad3e2b2681b49c46bd1808bfbe1217c2949341300e1194940143f3e1da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherentVandermonde4_norm_le
    (a : Fin 4 → ℂ)
    (h01 : ‖a 0‖ ≤ ‖a 1‖) (h12 : ‖a 1‖ ≤ ‖a 2‖)
    (h23 : ‖a 2‖ ≤ ‖a 3‖) :
    ‖coherentVandermonde4 a‖ ≤ 24 * ‖a 1‖ * ‖a 2‖^2 * ‖a 3‖^3 := by sorry

end D1Bound5
end
