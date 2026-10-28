-- Prove2me | Theorems.Thm_D1Bound5_first_pair_geometry_bounds
-- name    : D1Bound5.first_pair_geometry_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:45:04.805119+00:00
-- url     : https://prove2.me/theorems/e778394f-3dc0-4801-856b-84e6faa31f99
-- title:
--   First pair geometry bounds
-- statement:
--   Actual complex distance geometry for all first-pair rows with S≥15. The same b-s distance controls both the Vandermonde and the relabeled N3 residual, so no independent worst-case replacement is introduced.
-- source:
--   D1Bound5/FirstPairGeometry.lean, lines 18-101, SHA-256 6897ed712974dd8aa38c4f747975287a62389b141930051223663f4f1d136bb9. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.GCongr
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometry_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.first_pair_geometry_bounds (a b s : ℂ) (A1 B1 d1 : ℝ)
    (hb : b ≠ 0) (hBS : ‖b‖ ≤ ‖s‖) (hS15 : 15 ≤ ‖s‖)
    (hA1 : ‖a‖ ≤ A1) (hB1 : ‖b‖ ≤ B1)
    (hd1 : ‖a-b‖/‖b‖ ≤ d1) :
    let Q := ‖coherentVandermonde3 (![a,b,s] : Fin 3 → ℂ)‖/(‖b‖*‖s‖^2)
    Q ≤ d1*(1+A1/15)*(1+B1/15) ∧
      Q^2*firstPairPhi b s ≤
        (‖a-b‖^2/‖b‖^2)*(1+A1/15)^2*(1+B1/15)^8 := by sorry

end D1Bound5
end
