-- Prove2me | Theorems.Thm_ChromaticReconstruction_psum_one_of_two_big
-- name    : ChromaticReconstruction.psum_one_of_two_big
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:41:52.440515+00:00
-- url     : https://prove2.me/theorems/73e85650-e134-441f-ba53-ba1bf7b9090a
-- title:
--   Chromatic Reconstruction: psum one of two big
-- statement:
--   The Chromatic Reconstruction construction uses the psum one of two big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L165-L186
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoverP.lean#L165-L186

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.psum_one_of_two_big {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a : ℕ}
    (hb : bigWeights W = {a}) :
    psum 1 W = 2 * ((Multiset.card W : ℤ) - W.count a) + a * W.count a := by sorry
