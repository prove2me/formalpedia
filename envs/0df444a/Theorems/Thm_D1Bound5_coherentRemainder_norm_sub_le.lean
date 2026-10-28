-- Prove2me | Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
-- name    : D1Bound5.coherentRemainder_norm_sub_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:18.591816+00:00
-- url     : https://prove2.me/theorems/bdf50a83-53e7-4494-9828-e1ebdc5c1201
-- title:
--   Coherent Remainder norm sub le
-- statement:
--   The manuscript tail estimate applied directly to the remainder in the actual coherent form.
-- source:
--   D1Bound5/CoherentFormBounds.lean, lines 50-63, SHA-256 c03d23c1aa78f01b328715b302c1ec28dd87b243d972f665963735dee00e4981. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5






theorem _root_.D1Bound5.coherentRemainder_norm_sub_le
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m) (p q : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ ≤ 1 / P) (hq : ‖q⁻¹‖ ≤ 1 / P) (hAP : 1 < A * P) :
    ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) / P ^ m *
        (1 / (1 - 1 / (A * P)) ^ m - 1) := by sorry



end D1Bound5
end
