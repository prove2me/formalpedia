-- Prove2me | Theorems.Thm_ChromaticReconstruction_coeff_fP_lowerAt
-- name    : ChromaticReconstruction.coeff_fP_lowerAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:33:22.476854+00:00
-- url     : https://prove2.me/theorems/930beeba-621a-4aae-adb4-0700e0844751
-- title:
--   Chromatic Reconstruction: coeff f P lower At
-- statement:
--   The Chromatic Reconstruction construction uses the coeff f P lower At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L58-L68
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L58-L68

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.coeff_fP_lowerAt {W : Multiset ℕ} {a : ℕ} (ha : a ∈ bigWeights W) :
    coeff (Multiset.toFinsupp (lowerAt W a)) (fP W) = (((a - 1) * W.count a : ℕ) : ℚ) := by sorry
