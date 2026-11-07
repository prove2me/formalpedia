-- Prove2me | Theorems.Thm_EulerSparsify_fact_3_3
-- name    : EulerSparsify.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:17.3362+00:00
-- url     : https://prove2.me/theorems/99ddf79a-312a-4112-a060-e6969784d92b
-- title:
--   Fact 3.3 — changing the reference Laplacian costs a factor $1+\varepsilon$
-- statement:
--   Let $G$ and $H$ be connected weighted graphs with nonnegative weights on the same vertex set $V$, and suppose
--
--   $$\bigl\|L_G^{\dagger/2}(L_G-L_H)L_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le\varepsilon .$$
--
--   Then for every $M\in\mathbb R^{V\times V}$,
--
--   $$\bigl\|L_G^{\dagger/2}ML_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le(1+\varepsilon)\,\bigl\|L_H^{\dagger/2}ML_H^{\dagger/2}\bigr\|_{\mathrm{op}} .$$
--
--   **Formalization Note** $G$ and $H$ may have different edge sets; connected means through positive-weight edges.
--
--   Differences from the source:
--   - reading: "connected graphs" → connected through edges of positive weight; V may be empty; reason: a zero-weight edge is no edge of the weighted graph; for empty V both sides are 0
--   - generalization: graphs G, H → parallel edges and self-loops allowed; reason: a self-loop contributes nothing to a Laplacian
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Fact 3.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_lap
import Definitions.Def_EulerSparsify_DiGraph_Reach
import Definitions.Def_EulerSparsify_sqrtPinv
import Definitions.Def_LiqPremiaEq_opNorm

namespace EulerSparsify

/-- **Fact 3.3**, p.10, PDF p.12.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Fact 3.3: "Suppose G, H are connected graphs on the same vertex set V, and
‖L_G^{†/2} (L_G − L_H) L_G^{†/2}‖_op ≤ ε. Then for any M ∈ ℝ^{V×V}, we have
‖L_G^{†/2} M L_G^{†/2}‖_op ≤ (1 + ε)‖L_H^{†/2} M L_H^{†/2}‖_op."

**Formalization Note.** `G`, `H` are undirected weighted graphs on the vertex type `V` with their
own edge types and nonnegative weights; connected means through positive-weight edges
(`DiGraph.IsConnected`). Parallel edges and self-loops are allowed (a loop contributes nothing to a
Laplacian). `ε` is any real. -/
theorem fact_3_3 {V E F : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] (G : DiGraph V E) (H : DiGraph V F)
    (hG : ∀ e, 0 ≤ G.w e) (hH : ∀ f, 0 ≤ H.w f) (hGc : G.IsConnected) (hHc : H.IsConnected)
    (ε : ℝ) (hε : LiqPremiaEq.opNorm (sqrtPinv G.lap * (G.lap - H.lap) * sqrtPinv G.lap) ≤ ε)
    (M : Matrix V V ℝ) :
    LiqPremiaEq.opNorm (sqrtPinv G.lap * M * sqrtPinv G.lap) ≤
      (1 + ε) * LiqPremiaEq.opNorm (sqrtPinv H.lap * M * sqrtPinv H.lap) := by sorry

end EulerSparsify
