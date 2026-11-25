-- Prove2me | Theorems.Thm_ChromaticReconstruction_homogeneousComponent_phi_leafExt
-- name    : ChromaticReconstruction.homogeneousComponent_phi_leafExt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:12:53.434351+00:00
-- url     : https://prove2.me/theorems/c4ef8727-1fc5-497a-927a-d43d7263232e
-- title:
--   Chromatic Reconstruction: homogeneous Component phi leaf Ext
-- statement:
--   The Chromatic Reconstruction construction uses the homogeneous Component phi leaf Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Recovery.lean#L177-L193
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Recovery.lean#L177-L193

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable (S : SimpleGraph K) (m : K → ℕ)

theorem ChromaticReconstruction.homogeneousComponent_phi_leafExt (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    homogeneousComponent j (phi (leafExt S m)) =
      ∑ F ∈ S.edgeFinset.powerset.filter
          (fun F : Finset (Sym2 K) => (compSets (F : Set (Sym2 K))).card = j),
        (-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F := by sorry
