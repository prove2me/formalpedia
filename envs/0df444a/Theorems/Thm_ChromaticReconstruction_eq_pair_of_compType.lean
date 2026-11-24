-- Prove2me | Theorems.Thm_ChromaticReconstruction_eq_pair_of_compType
-- name    : ChromaticReconstruction.eq_pair_of_compType
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:10:42.270815+00:00
-- url     : https://prove2.me/theorems/7d8ac845-657d-4658-a430-e7441f4b4d7b
-- title:
--   Chromatic Reconstruction: eq pair of comp Type
-- statement:
--   If the component type is `(2, 1, …, 1)`, the (loopless) edge set is a single edge.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L191-L268
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L191-L268

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.eq_pair_of_compType {A : Finset (Sym2 V)} (hA : ∀ e ∈ A, ¬ e.IsDiag) {s : ℕ}
    (h : compType (A : Set (Sym2 V)) = 2 ::ₘ Multiset.replicate s 1) :
    ∃ u v, u ≠ v ∧ A = {s(u, v)} := by sorry
