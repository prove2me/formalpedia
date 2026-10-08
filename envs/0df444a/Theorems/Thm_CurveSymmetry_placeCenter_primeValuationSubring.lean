-- Prove2me | Theorems.Thm_CurveSymmetry_placeCenter_primeValuationSubring
-- name    : CurveSymmetry.placeCenter_primeValuationSubring
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.227927+00:00
-- url     : https://prove2.me/theorems/071a639b-155d-4270-ae34-55f36ff68e03
-- title:
--   The center of the localization $A_{\mathfrak p}$ of a Dedekind domain at a nonzero prime $\mathfrak p$ is $\mathfrak p$
-- statement:
--   Let $A$ be a Dedekind domain with field of fractions $K$, and identify $A$ with its image in $K$. For a nonzero prime ideal $\mathfrak p$ of $A$, let $A_{\mathfrak p}=\{a/s:\ a\in A,\ s\in A\setminus\mathfrak p\}\subseteq K$ be the localization, a valuation subring of $K$. For a valuation subring $\mathcal O$ of $K$ containing $A$, with maximal ideal $\mathfrak m_{\mathcal O}$, call $\mathfrak c(\mathcal O)=\{a\in A:\ a\in\mathfrak m_{\mathcal O}\}$ its center in $A$. Then
--
--   $$
--   \mathfrak c(A_{\mathfrak p})=\mathfrak p.
--   $$
--
--   Together with the converse (a valuation subring of $K$ containing $A$ and different from $K$ is the localization at its center), this matches the places of $K$ containing $A$ with the nonzero primes of $A$. It is applied to the coordinate ring of the double cover (7) to classify the places of its function field, for Lemma 4 and Remark 5.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/DedekindPlaces.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

open CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

theorem CurveSymmetry.placeCenter_primeValuationSubring (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    placeCenter K (primeValuationSubring K P hP) (algebraMap_mem_primeValuationSubring hP) = P := by sorry
