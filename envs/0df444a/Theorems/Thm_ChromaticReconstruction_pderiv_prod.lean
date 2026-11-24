-- Prove2me | Theorems.Thm_ChromaticReconstruction_pderiv_prod
-- name    : ChromaticReconstruction.pderiv_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:28:38.227771+00:00
-- url     : https://prove2.me/theorems/d3a53820-b793-4a66-abe8-f8bd232ba1d4
-- title:
--   Chromatic Reconstruction: pderiv prod
-- statement:
--   Leibniz rule for finite products.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PhiFormula.lean#L24-L36
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PhiFormula.lean#L24-L36

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.pderiv_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℚ) (i : ℕ) :
    pderiv i (∏ x ∈ s, f x) = ∑ x ∈ s, (∏ y ∈ s.erase x, f y) * pderiv i (f x) := by sorry
