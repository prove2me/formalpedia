-- Prove2me | Theorems.Thm_ChromaticReconstruction_exists_partner
-- name    : ChromaticReconstruction.exists_partner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:35:31.15345+00:00
-- url     : https://prove2.me/theorems/f17fbbdd-8e45-4771-9fc8-4e8b845ea744
-- title:
--   Chromatic Reconstruction: exists partner
-- statement:
--   If `fP W = fP W'`, every big weight of `W` has a partner in `W'`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L87-L102
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L87-L102

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.exists_partner {W W' : Multiset ℕ} (h : fP W = fP W') {a : ℕ} (ha : a ∈ bigWeights W) :
    ∃ a' ∈ bigWeights W', lowerAt W a = lowerAt W' a' ∧
      (a - 1) * W.count a = (a' - 1) * W'.count a' := by sorry
