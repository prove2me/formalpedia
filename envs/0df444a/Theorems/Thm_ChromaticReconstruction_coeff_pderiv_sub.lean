-- Prove2me | Theorems.Thm_ChromaticReconstruction_coeff_pderiv_sub
-- name    : ChromaticReconstruction.coeff_pderiv_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:30:51.735998+00:00
-- url     : https://prove2.me/theorems/30986872-8a61-462b-b55a-15ea9b951bb6
-- title:
--   Chromatic Reconstruction: coeff pderiv sub
-- statement:
--   Coefficients of a partial derivative.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L275-L294
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L275-L294

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.coeff_pderiv_sub (f : MvPolynomial ℕ ℚ) (r : ℕ) (d : ℕ →₀ ℕ) (hd : 1 ≤ d r) :
    coeff (d - Finsupp.single r 1) (pderiv r f) = d r * coeff d f := by sorry
