-- Prove2me | Theorems.Thm_ChromaticReconstruction_layer_tree
-- name    : ChromaticReconstruction.layer_tree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:27:19.772028+00:00
-- url     : https://prove2.me/theorems/44c0ed04-3968-4ac1-a785-0873b40c43d4
-- title:
--   Chromatic Reconstruction: layer tree
-- statement:
--   The Chromatic Reconstruction construction uses the layer tree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L19-L35
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L19-L35

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)

theorem ChromaticReconstruction.layer_tree (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    homogeneousComponent j (phi (leafExt S m)) =
      ∑ F ∈ S.edgeFinset.powerset.filter
          (fun F : Finset (Sym2 K) => Fintype.card K = j + F.card),
        (-1) ^ ((∑ i, m i) - 1 + F.card) * masterTerm m F := by sorry
