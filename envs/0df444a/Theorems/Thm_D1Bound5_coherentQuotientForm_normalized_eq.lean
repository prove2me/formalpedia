-- Prove2me | Theorems.Thm_D1Bound5_coherentQuotientForm_normalized_eq
-- name    : D1Bound5.coherentQuotientForm_normalized_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:12.452992+00:00
-- url     : https://prove2.me/theorems/93f059a9-5ab9-4227-bca8-fbf8280182b3
-- title:
--   Coherent Quotient Form normalized eq
-- statement:
--   The normalized exact identity for the actual manuscript form, including the precise coherent branch choices and all quotient weights.
-- source:
--   D1Bound5/CoherentFormBounds.lean, lines 16-48, SHA-256 c03d23c1aa78f01b328715b302c1ec28dd87b243d972f665963735dee00e4981. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.coherentQuotientForm_normalized_eq
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (Delta p q eta : ℂ) (hDelta : Delta ≠ 0) (heta : eta ≠ 0)
    (hp : ∀ i, ‖p⁻¹ * (a i)⁻¹‖ < 1)
    (hq : ∀ i, ‖q⁻¹ * (a i)⁻¹‖ < 1) :
    coherentQuotientForm a Delta p q eta / (Delta * eta) =
      1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) +
        ((-1 : ℂ) ^ (m - 1) * (∏ i, a i)⁻¹) * coherentRemainder a p q := by sorry





end D1Bound5
end
