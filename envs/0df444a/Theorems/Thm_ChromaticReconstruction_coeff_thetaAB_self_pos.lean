-- Prove2me | Theorems.Thm_ChromaticReconstruction_coeff_thetaAB_self_pos
-- name    : ChromaticReconstruction.coeff_thetaAB_self_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:58:31.962796+00:00
-- url     : https://prove2.me/theorems/26f01e75-da1f-4a56-b2bb-aed7a61f77f3
-- title:
--   Chromatic Reconstruction: coeff theta AB self pos
-- statement:
--   The Chromatic Reconstruction construction uses the coeff theta AB self pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L161-L173
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L161-L173

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.coeff_thetaAB_self_pos {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a b : ℕ}
    (hab : {a, b} ≤ W) :
    0 < coeff (Multiset.toFinsupp ((a + b - 1) ::ₘ (W - {a, b}))) (thetaAB W a b) := by sorry
