-- Prove2me | Theorems.Thm_D1Bound5_full_ring_coherent_four_one_le_norm
-- name    : D1Bound5.full_ring_coherent_four_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:48.743316+00:00
-- url     : https://prove2.me/theorems/fbc7bafe-19f5-46a6-9102-aeda751aa53e
-- title:
--   Full ring coherent four one le norm
-- statement:
--   The true four-anchor coherent form has the full-ring lower bound.
-- source:
--   D1Bound5/CoherentQuotientForms.lean, lines 95-115, SHA-256 392bcc4a54c87594a3594b5daa5b4ef8fcad70a5934eefb672cd5a7b190f86a4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5










theorem _root_.D1Bound5.full_ring_coherent_four_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {p q : 𝓞 K}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (a : Fin 4 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (phi ((coherentVandermonde4 a : 𝓞 K) : K)) (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 ≤ ‖coherentQuotientForm (fun i => phi (a i : K))
      (phi ((coherentVandermonde4 a : 𝓞 K) : K)) (phi (p : K)) (phi (q : K)) eta‖ := by sorry

end D1Bound5
end
