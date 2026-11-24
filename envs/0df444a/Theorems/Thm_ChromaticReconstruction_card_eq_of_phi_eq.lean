-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_eq_of_phi_eq
-- name    : ChromaticReconstruction.card_eq_of_phi_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:25:17.146051+00:00
-- url     : https://prove2.me/theorems/cf51d3de-3323-469a-87fc-20a2cf6db923
-- title:
--   Chromatic Reconstruction: card eq of phi eq
-- statement:
--   The Chromatic Reconstruction construction uses the card eq of phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L89-L100
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L89-L100

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]

theorem ChromaticReconstruction.card_eq_of_phi_eq {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.Connected)
    (h : phi (uniformLeafExt q G) = phi (uniformLeafExt q H)) :
    Fintype.card V = Fintype.card W := by sorry
