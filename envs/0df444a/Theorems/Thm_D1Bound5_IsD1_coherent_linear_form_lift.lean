-- Prove2me | Theorems.Thm_D1Bound5_IsD1_coherent_linear_form_lift
-- name    : D1Bound5.IsD1.coherent_linear_form_lift
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:32.079118+00:00
-- url     : https://prove2.me/theorems/32822c74-1ff0-408a-aa5f-c63483be5348
-- title:
--   Is D1 — coherent linear form lift
-- statement:
--   Any polynomial-weighted coherent linear form on actual tuple roots lifts to the original ring. This supplies the arithmetic bridge after the explicit Vandermonde quotient weights have been simplified.
-- source:
--   D1Bound5/CoherentIntegralForms.lean, lines 73-92, SHA-256 81e6a044e834ea1f7a20cfce931dfefd9cdd8cbc6a1dc7467c69328d64c38e4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5












theorem _root_.D1Bound5.IsD1.coherent_linear_form_lift
    {R ι : Type*} [CommRing R] [Fintype ι]
    (f : R →+* ℂ) (hf : Function.Injective f)
    {T : Finset R} (hT : IsD1 T) {p q : R}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (a c : ι → R) (Delta : R)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = f p * f q) :
    ∃ L : R, f L =
      -f Delta * coherentTerminalRoot (f p) (f q) eta +
        ∑ i, f (c i) * coherentAnchorRoot (f (a i)) (f p) (f q) eta := by sorry



end D1Bound5
end
