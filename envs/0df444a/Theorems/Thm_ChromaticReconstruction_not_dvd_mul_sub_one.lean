-- Prove2me | Theorems.Thm_ChromaticReconstruction_not_dvd_mul_sub_one
-- name    : ChromaticReconstruction.not_dvd_mul_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:34:02.820563+00:00
-- url     : https://prove2.me/theorems/20ce7bf8-9b5f-485d-b42a-2f8c54cebf3d
-- title:
--   Chromatic Reconstruction: not dvd mul sub one
-- statement:
--   The Chromatic Reconstruction construction uses the not dvd mul sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L121-L128
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L121-L128

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.not_dvd_mul_sub_one {q r : ℕ} (hq : 2 ≤ q) (hr : 1 ≤ r) (x : ℕ) : q * x ≠ q * r - 1 := by sorry
