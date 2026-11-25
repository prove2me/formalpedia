-- Prove2me | Theorems.Thm_ChromaticReconstruction_eq_two_of_not_big
-- name    : ChromaticReconstruction.eq_two_of_not_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:37:50.266615+00:00
-- url     : https://prove2.me/theorems/e4a879a0-a73b-4e4e-8315-df7737a3073a
-- title:
--   Chromatic Reconstruction: eq two of not big
-- statement:
--   The Chromatic Reconstruction construction uses the eq two of not big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L153-L158
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L153-L158

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.eq_two_of_not_big {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {x : ℕ} (hx : x ∈ W)
    (hnb : x ∉ bigWeights W) : x = 2 := by sorry
