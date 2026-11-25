-- Prove2me | Theorems.Thm_ChromaticReconstruction_phi_uniformLeafExt_eq_iff
-- name    : ChromaticReconstruction.phi_uniformLeafExt_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:45.70835+00:00
-- url     : https://prove2.me/theorems/75fe5080-d86a-4284-8f6f-e9115b95fbab
-- title:
--   Chromatic Reconstruction: phi uniform Leaf Ext eq iff
-- statement:
--   **Theorem 2.** For fixed `q ≥ 2` and finite connected graphs `G, H`,
--   `Φ_{C_q(G)} = Φ_{C_q(H)}` if and only if `X_G = X_H`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/MainTheorems.lean#L45-L48
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/MainTheorems.lean#L45-L48

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Theorem2
import Definitions.Def_RequestProject_ProperTree
import Definitions.Def_RequestProject_CountingLimit
import Definitions.Def_RequestProject_TauBound
import Definitions.Def_RequestProject_MainTheorems
set_option autoImplicit true
open MvPolynomial Finset Filter Topology
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.phi_uniformLeafExt_eq_iff {V W : Type*} [Fintype V] [Fintype W] (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Connected) (hH : H.Connected) :
    phi (uniformLeafExt q G) = phi (uniformLeafExt q H) ↔ chromSymm G = chromSymm H := by sorry
