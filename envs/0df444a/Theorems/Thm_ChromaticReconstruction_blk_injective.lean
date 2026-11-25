-- Prove2me | Theorems.Thm_ChromaticReconstruction_blk_injective
-- name    : ChromaticReconstruction.blk_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:22:11.917094+00:00
-- url     : https://prove2.me/theorems/4eeeeb6f-aba5-41ef-8f4a-a7439f1c73a2
-- title:
--   Chromatic Reconstruction: blk injective
-- statement:
--   The Chromatic Reconstruction construction uses the blk injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L231-L235
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L231-L235

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.blk_injective (l0 : Σ i, Fin (m i)) : Function.Injective (blk m l0) := by sorry
