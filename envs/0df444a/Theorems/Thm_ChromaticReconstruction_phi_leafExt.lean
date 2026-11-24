-- Prove2me | Theorems.Thm_ChromaticReconstruction_phi_leafExt
-- name    : ChromaticReconstruction.phi_leafExt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:32:49.634683+00:00
-- url     : https://prove2.me/theorems/2e016b68-94a8-43ef-87e5-3bca32f57829
-- title:
--   Chromatic Reconstruction: phi leaf Ext
-- statement:
--   **Master formula** for leaf extensions (index form): if every vertex `i` of `S` receives
--   `m i ≥ 1` new leaves, then
--   `Φ = ∑_{leaves l₀} ∑_{F ⊆ E(S)} (-1)^{L - 1 + |F|} π(∏_{C ∈ Comp(F)} p_{w(C) - [l₀ ∈ C]})`,
--   where `L = ∑ m i` and `w(C) = ∑_{i ∈ C} (m i + 1)`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L348-L362
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L348-L362

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.phi_leafExt (hm : ∀ i, 1 ≤ m i) :
    phi (leafExt S m) = ∑ l0 : Σ i, Fin (m i), ∑ F ∈ S.edgeFinset.powerset,
      (-1) ^ ((∑ i, m i) - 1 + F.card) * killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0)) := by sorry
