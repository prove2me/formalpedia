-- Prove2me | Theorems.Thm_EulerSparsify_fact_3_4
-- name    : EulerSparsify.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:41.447135+00:00
-- url     : https://prove2.me/theorems/e2f14e68-cf7e-4940-8ee3-3306dc283aea
-- title:
--   Fact 3.4 — with equal degrees, the undirected error is at most twice the directed error
-- statement:
--   Let $\vec G=(V,E,w_{\vec G})$ and $\vec H=(V,F,w_{\vec H})$ be directed graphs with nonnegative weights on the same vertex set, and let $G=\mathrm{und}(\vec G)$, $H=\mathrm{und}(\vec H)$. If $B_{\vec G}^\top w_{\vec G}=B_{\vec H}^\top w_{\vec H}$, then
--
--   $$\bigl\|L_G^{\dagger/2}(L_G-L_H)L_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le2\,\bigl\|L_G^{\dagger/2}(\vec L_{\vec G}-\vec L_{\vec H})L_G^{\dagger/2}\bigr\|_{\mathrm{op}} .$$
--
--   In particular an Eulerian spectral approximation also approximates the undirected Laplacian, which the proof of Theorem 5.11 uses to keep the reference Laplacian stable across rounds.
--
--   Differences from the source:
--   - generalization: graphs ⃗G, ⃗H → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B and contributes nothing to L, the directed Laplacian or Bᵀw
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Fact 3.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_dirLap
import Definitions.Def_EulerSparsify_sqrtPinv
import Definitions.Def_LiqPremiaEq_opNorm

namespace EulerSparsify

/-- **Fact 3.4**, p.10, PDF p.12.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Fact 3.4: "Suppose ⃗G = (V, E, w_⃗G), ⃗H = (V, F, w_⃗H) share the same vertex set and
G := und(⃗G), H := und(⃗H). If Bᵀ_⃗G w_⃗G = Bᵀ_⃗H w_⃗H, then
‖L_G^{†/2}(L_G − L_H)L_G^{†/2}‖_op ≤ 2‖L_G^{†/2}(⃗L_⃗G − ⃗L_⃗H)L_G^{†/2}‖_op."

**Formalization Note.** Two edge types `E`, `F` as in the statement; nonnegative weights (the
paper's convention for graphs); parallel edges and self-loops allowed. `L_G = G.lap`, `L_H = H.lap`,
`⃗L = DiGraph.dirLap`. -/
theorem fact_3_4 {V E F : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] (G : DiGraph V E) (H : DiGraph V F)
    (hG : ∀ e, 0 ≤ G.w e) (hH : ∀ f, 0 ≤ H.w f)
    (hB : G.incMat.transpose.mulVec G.w = H.incMat.transpose.mulVec H.w) :
    LiqPremiaEq.opNorm (sqrtPinv G.lap * (G.lap - H.lap) * sqrtPinv G.lap) ≤
      2 * LiqPremiaEq.opNorm (sqrtPinv G.lap * (G.dirLap - H.dirLap) * sqrtPinv G.lap) := by sorry

end EulerSparsify
