-- Prove2me | Theorems.Thm_ChromaticReconstruction_leafExt_recovery
-- name    : ChromaticReconstruction.leafExt_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:26:37.580203+00:00
-- url     : https://prove2.me/theorems/6672ea41-d9df-40c1-817c-573fe5a08b4b
-- title:
--   Chromatic Reconstruction: leaf Ext recovery
-- statement:
--   **Lemma recovery.** If the leaf extensions of two trees (with at least one new leaf at each
--   vertex and at least three vertices) have the same `Φ`, then they have the same number of skeleton
--   vertices, the same weight multiset and the same multiset of edge types.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L121-L176
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L121-L176

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)

theorem ChromaticReconstruction.leafExt_recovery {K' : Type*} [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
    (hS : S.IsTree) (hS' : S'.IsTree) {m : K → ℕ} {m' : K' → ℕ} (hm : ∀ i, 1 ≤ m i)
    (hm' : ∀ i, 1 ≤ m' i) (hn : 3 ≤ Fintype.card K + ∑ i, m i)
    (hn' : 3 ≤ Fintype.card K' + ∑ i, m' i) (h : phi (leafExt S m) = phi (leafExt S' m')) :
    Fintype.card K = Fintype.card K' ∧ weightMS m = weightMS m' ∧
      edgeTypes S (fun i => m i + 1) = edgeTypes S' (fun i => m' i + 1) := by sorry
