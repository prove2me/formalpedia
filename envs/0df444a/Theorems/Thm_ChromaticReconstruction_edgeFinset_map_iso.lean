-- Prove2me | Theorems.Thm_ChromaticReconstruction_edgeFinset_map_iso
-- name    : ChromaticReconstruction.edgeFinset_map_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:28:43.585953+00:00
-- url     : https://prove2.me/theorems/628c629f-45af-4040-a5d5-f1eba57bc29d
-- title:
--   Chromatic Reconstruction: edge Finset map iso
-- statement:
--   The Chromatic Reconstruction construction uses the edge Finset map iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L175-L193
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L175-L193

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]

theorem ChromaticReconstruction.edgeFinset_map_iso {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') :
    G'.edgeFinset = G.edgeFinset.map e.toEquiv.toEmbedding.sym2Map := by sorry
