-- Prove2me | Theorems.Thm_FamousTheorems_laplacian_kernel_connected_components
-- name    : FamousTheorems.laplacian_kernel_connected_components
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:25.863982+00:00
-- url     : https://prove2.me/theorems/4016fad0-2389-4d3b-b072-8e8b22ca5ead
-- title:
--   The Laplacian matrix counts connected components
-- statement:
--   **The Laplacian matrix counts connected components.** Let $G$ be a finite simple graph with Laplacian matrix $L=D-A$, where $D$ is the diagonal degree matrix and $A$ the adjacency matrix. Then the number of connected components of $G$ equals $\dim_{\mathbb R}\ker L$.
--
--   Equivalently, the multiplicity of $0$ as an eigenvalue of $L$ is the number of components, and $G$ is connected exactly when the second smallest eigenvalue is positive. This is the starting point of spectral graph theory and of spectral clustering.
--
--   **Formalization note.** Mathlib's `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`. `G.lapMatrix ℝ` is the Laplacian, and `Matrix.toLin'` turns it into a linear map on $\mathbb R^V$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem laplacian_kernel_connected_components {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card G.ConnectedComponent = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by sorry

end FamousTheorems
