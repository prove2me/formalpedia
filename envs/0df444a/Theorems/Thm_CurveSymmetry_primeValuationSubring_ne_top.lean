-- Prove2me | Theorems.Thm_CurveSymmetry_primeValuationSubring_ne_top
-- name    : CurveSymmetry.primeValuationSubring_ne_top
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:44.916109+00:00
-- url     : https://prove2.me/theorems/1fcbec71-a820-46cc-ae03-01bab22ceed5
-- title:
--   The localization of a Dedekind domain at a nonzero prime is a proper subring of the fraction field
-- statement:
--   Let $A$ be a Dedekind domain with field of fractions $K$, and let $\mathfrak p$ be a nonzero prime ideal of $A$. Then the localization $A_{\mathfrak p}=\{a/s:\ a\in A,\ s\in A\setminus\mathfrak p\}$, a valuation subring of $K$, is not all of $K$:
--
--   $$
--   A_{\mathfrak p}\ne K.
--   $$
--
--   Thus $A_{\mathfrak p}$ is a place of $K$ in the sense used throughout, a valuation subring different from the whole field. It is used in the classification of the places of the function field of the double cover (7), for Lemma 4 and Remark 5.
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

theorem CurveSymmetry.primeValuationSubring_ne_top (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    primeValuationSubring K P hP ≠ ⊤ := by sorry
