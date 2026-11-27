-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_lemma_4_11
-- name    : BilevelSOC.SecondOrder.Supplement.lemma_4_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:47:41.861567+00:00
-- url     : https://prove2.me/theorems/321d2cbb-8bca-4747-888d-9617f6fcc503
-- title:
--   Lemma 4.11 — Normal-graph tangent upper estimate, including equality under metric subregularity
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions and Assumption 4.10: every $f(x,\cdot)$ is convex, and $g$ is independent of $x$ and componentwise convex. Let $K=\{y:g(y)\le0\}$ and $z=(\bar x,\bar y)\in\operatorname{gph}S$. Define
--
--   $$H=\{(\delta_x,\delta_y):(\delta_y,-\nabla^2_{yx}f(z)\delta_x-\nabla^2_{yy}f(z)\delta_y)\in T_{\operatorname{gph}\widehat N_K}(\bar y,-\nabla_yf(z))\}.$$
--
--   Then $T_{\operatorname{gph}S}(z)\subseteq H$. Equality holds if $(x,y)\mapsto\operatorname{gph}\widehat N_K-\{(y,-\nabla_yf(x,y))\}$ is metrically subregular at $(z,0,0)$. This normal-graph support includes both the unconditional inclusion and conditional equality, with the complete graph and residual mapping.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - encoding: Euclidean normal graph and ordinary distance inequality → partial y gradients and their joint derivatives, complete normal graph and translated map, and extended-distance subregularity; reason: empty images retain distance +∞; on nonempty images these are the ordinary distances, and equivalent product norms preserve existence of κ>0
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 14, Lemma 4.11

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_NormalGraph
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem lemma_4_11 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hconvex : FixedConvexLower D)
    (hsol : z.2 ∈ solMap D z.1) :
    tangentCone (graph (solMap D)) z ⊆ normalTangentEstimate D z ∧
    (MetricSubregularAt (normalResidual D) z 0 →
      tangentCone (graph (solMap D)) z = normalTangentEstimate D z) := by sorry
end BilevelSOC.SecondOrder.Supplement
