-- Prove2me | Theorems.Thm_D1Bound5_full_ring_three_general_window
-- name    : D1Bound5.full_ring_three_general_window
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:11.127981+00:00
-- url     : https://prove2.me/theorems/63999718-25b8-4db1-b86f-f56388ab8598
-- title:
--   Full ring three general window
-- statement:
--   Nonzero general three-anchor forms in the full integer ring exclude the general-three window. Integrality is supplied from actual D(1) entries and the coherent square roots; it is not an external premise.
-- source:
--   D1Bound5/ThreeGeneralWindow.lean, lines 42-99, SHA-256 672e1e3d605f06db37de02cec597d627f04713038fc2c51993a56e88102920bc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.full_ring_three_general_window
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 3 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hP : 4*‖phi (a 2 : K)‖ ≤ ‖phi (p : K)‖)
    (hAP : 9 ≤ ‖phi (a 0 : K)‖*‖phi (p : K)‖)
    (hQ : ‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hPQ : 4000 ≤ ‖phi (p : K)‖*‖phi (q : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (coherentVandermonde3 (fun i => phi (a i : K)))
        (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    ‖phi (q : K)‖ < 101*‖phi (a 1 : K)‖^2*‖phi (a 2 : K)‖^4/‖phi (p : K)‖ ∨
      ‖phi (a 0 : K)‖^2*‖phi (p : K)‖^5/(37*‖phi (a 2 : K)‖^2) < ‖phi (q : K)‖ := by sorry

end D1Bound5
end
