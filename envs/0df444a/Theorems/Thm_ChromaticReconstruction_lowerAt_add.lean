-- Prove2me | Theorems.Thm_ChromaticReconstruction_lowerAt_add
-- name    : ChromaticReconstruction.lowerAt_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:24:52.469175+00:00
-- url     : https://prove2.me/theorems/27b7d957-8323-4334-a7fb-219e4a006f10
-- title:
--   Chromatic Reconstruction: lower At add
-- statement:
--   The Chromatic Reconstruction construction uses the lower At add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L37-L43
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L37-L43

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.lowerAt_add {W : Multiset ℕ} {a : ℕ} (ha : a ∈ W) :
    lowerAt W a + {a} = W + {a - 1} := by sorry
