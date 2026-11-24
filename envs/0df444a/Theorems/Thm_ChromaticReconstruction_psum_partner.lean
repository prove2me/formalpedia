-- Prove2me | Theorems.Thm_ChromaticReconstruction_psum_partner
-- name    : ChromaticReconstruction.psum_partner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:36:27.15722+00:00
-- url     : https://prove2.me/theorems/f4de6a0a-a794-421e-b17d-d87f3299e619
-- title:
--   Chromatic Reconstruction: psum partner
-- statement:
--   The power-sum relation between partners.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L113-L121
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L113-L121

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.psum_partner {W W' : Multiset ℕ} {a a' : ℕ} (ha : a ∈ W) (ha' : a' ∈ W') (h1 : 1 ≤ a)
    (h1' : 1 ≤ a') (h : lowerAt W a = lowerAt W' a') (j : ℕ) :
    psum j W - psum j W' = ((a' : ℤ) - 1) ^ j + (a : ℤ) ^ j - ((a : ℤ) - 1) ^ j - (a' : ℤ) ^ j := by sorry
