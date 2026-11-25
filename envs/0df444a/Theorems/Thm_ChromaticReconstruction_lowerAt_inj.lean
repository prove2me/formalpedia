-- Prove2me | Theorems.Thm_ChromaticReconstruction_lowerAt_inj
-- name    : ChromaticReconstruction.lowerAt_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:33:26.271079+00:00
-- url     : https://prove2.me/theorems/e7682bf3-84f6-4e20-87f8-3be9f0349010
-- title:
--   Chromatic Reconstruction: lower At inj
-- statement:
--   The Chromatic Reconstruction construction uses the lower At inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L45-L56
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L45-L56

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.lowerAt_inj {W : Multiset ℕ} {a b : ℕ} (ha : a ∈ W) (hb : b ∈ W) (ha1 : 1 ≤ a)
    (hb1 : 1 ≤ b) (h : lowerAt W a = lowerAt W b) : a = b := by sorry
