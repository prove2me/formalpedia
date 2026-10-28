-- Prove2me | Theorems.Thm_D1Bound5_IsD1_coherent_terminal_root_lift
-- name    : D1Bound5.IsD1.coherent_terminal_root_lift
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:31.470104+00:00
-- url     : https://prove2.me/theorems/2c9e99fe-b561-408c-a41a-27ccebc89ca8
-- title:
--   Is D1 — coherent terminal root lift
-- statement:
--   The coherent terminal root of two actual tuple entries lifts to the original ring, even though the auxiliary square root `eta` need not do so.
-- source:
--   D1Bound5/CoherentIntegralForms.lean, lines 28-47, SHA-256 81e6a044e834ea1f7a20cfce931dfefd9cdd8cbc6a1dc7467c69328d64c38e4c. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.IsD1.coherent_terminal_root_lift
    {R : Type*} [CommRing R] (f : R →+* ℂ) (hf : Function.Injective f)
    {T : Finset R} (hT : IsD1 T) {p q : R}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = f p * f q) :
    ∃ z : R, f z = coherentTerminalRoot (f p) (f q) eta := by sorry







end D1Bound5
end
