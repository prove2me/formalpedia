-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_layer_decomposition
-- name    : CaiZhuInfo.Matrix.layer_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:30.971843+00:00
-- url     : https://prove2.me/theorems/34e58f83-8d04-4f5b-8e7c-0b6bb22f1e77
-- title:
--   Lemma 4.1 — Layer decomposition
-- statement:
--   For a finitely supported law $Q$ on a discrete group, order its positive masses $q_1\ge\cdots\ge q_\ell>0$, set $q_{\ell+1}=0$, and define $A_j=\{g_1,\dots,g_j\}$ and $w_j=j(q_j-q_{j+1})$. Then
--   $$w_j\ge0,\qquad\sum_{j=1}^\ell w_j=1,\qquad Q=\sum_{j=1}^\ell w_jU_{A_j}.$$
--   The weights and layers are computed from $Q$ rather than assumed. The result provides the uniform-layer representation used by the entropy estimates.
--
--   Differences from the source:
--   - encoding: indices 1 through the positive support size → Fin indices i with source layer number i+1; reason: zero-based indexing represents exactly the same nested layers
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Lemma 4.1, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_LayerData

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem layer_decomposition {G : Type} [Group G] (L : LayerData G) :
    (∀ i, 0 ≤ L.weight i) ∧ (∑ i, L.weight i) = 1 ∧
    ∀ g, mass L.Q g = ∑ i, L.weight i * L.layerMass i g := by sorry

end CaiZhuInfo.Matrix
