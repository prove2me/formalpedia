-- Prove2me | Theorems.Thm_ChromaticReconstruction_phi_uniformLeafExt_eq
-- name    : ChromaticReconstruction.phi_uniformLeafExt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:30:39.0736+00:00
-- url     : https://prove2.me/theorems/bc1751d8-e319-4d13-999d-bfae08fca5bf
-- title:
--   Chromatic Reconstruction: phi uniform Leaf Ext eq
-- statement:
--   The Chromatic Reconstruction construction uses the phi uniform Leaf Ext eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L34-L66
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L34-L66

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.phi_uniformLeafExt_eq (q : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) :
    phi (uniformLeafExt q G) = ∑ F ∈ G.edgeFinset.powerset,
      (-1) ^ ((q - 1) * Fintype.card V - 1 + F.card) * ((q - 1 : ℕ) : ℚ) • innerSum q F := by sorry
