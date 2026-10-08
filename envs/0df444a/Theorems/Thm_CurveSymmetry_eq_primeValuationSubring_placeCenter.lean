-- Prove2me | Theorems.Thm_CurveSymmetry_eq_primeValuationSubring_placeCenter
-- name    : CurveSymmetry.eq_primeValuationSubring_placeCenter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:36.09715+00:00
-- url     : https://prove2.me/theorems/9f89c85f-9acd-497d-9db1-fecf63a06b53
-- title:
--   A valuation subring containing a Dedekind domain, other than the fraction field, is the localization at its center
-- statement:
--   Let $A$ be a Dedekind domain with field of fractions $K$, and identify $A$ with its image in $K$. Let $\mathcal O$ be a valuation subring of $K$ with $A\subseteq\mathcal O$ and $\mathcal O\ne K$, let $\mathfrak m_{\mathcal O}$ be its maximal ideal, and let $\mathfrak p=\{a\in A:\ a\in\mathfrak m_{\mathcal O}\}$ be its center in $A$, a nonzero prime ideal. Then $\mathcal O$ is the localization of $A$ at $\mathfrak p$:
--
--   $$
--   \mathcal O=A_{\mathfrak p}=\{a/s:\ a\in A,\ s\in A\setminus\mathfrak p\}.
--   $$
--
--   So every place of $K$ (a valuation subring other than $K$) that contains $A$ is the local ring of a nonzero prime of $A$. Applied to the coordinate ring of the double cover (7), it yields the places over the finite $t$-line used for Lemma 4 and Remark 5.
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

theorem CurveSymmetry.eq_primeValuationSubring_placeCenter (O : ValuationSubring K)
    (hO : ∀ a : A, algebraMap A K a ∈ O) (htop : O ≠ ⊤) :
    O = primeValuationSubring K (placeCenter K O hO) (placeCenter_ne_bot O hO htop) := by sorry
