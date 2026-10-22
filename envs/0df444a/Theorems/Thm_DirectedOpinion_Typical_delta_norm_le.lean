-- Prove2me | Theorems.Thm_DirectedOpinion_Typical_delta_norm_le
-- name    : DirectedOpinion.Typical.delta_norm_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:42.713915+00:00
-- url     : https://prove2.me/theorems/b37025fe-2d57-4558-80a4-7c777df7d83e
-- title:
--   Proof of Theorem 1, p. 22 — ‖Δ‖_∞ ≤ 1 − d
-- statement:
--   Let $G$ be a vertex-weighted directed graph whose weights $c(i,r)$ lie in $[0,1]$ and sum to $c$ at every vertex with $d_i^->0$, where $c\in[0,1)$, $d\in(0,1]$ and $c+d\le1$. Let $\Delta$ be the operator (10), $\Delta f(i)=\sum_{r=1}^{d_i^-}c(i,r)f(\ell(i,r))+(1-c-d)f(i)$. If $|f(v)|\le M$ for every vertex $v$, then for every vertex $i$
--   $$|\Delta f(i)|\le\sum_{r=1}^{d_i^-}c(i,r)M+(1-c-d)M\le(1-d)M .$$
--   Taking $M=\sup_v|f(v)|$ gives $\|\Delta\|_\infty\le1-d<1$: the operator is a contraction of $L^\infty(V)$, which drives both the stationarity of Theorem 1 and the error propagation in Theorem 2.
--
--   **Formalization Note** The page writes $\|f\|_\infty=\sup_vf(v)$; the absolute value is meant. The bound is stated for every bound $M$ on $|f|$ instead of through an operator norm on $L^\infty(V)$.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 22, proof of Theorem 1, display after the definition of ‖Δ‖_∞

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_Model

namespace DirectedOpinion.Typical

/-- Proof of Theorem 1, p. 22: `|Δf(i)| ≤ Σ_r c(i, r)‖f‖_∞ + (1 − c − d)‖f‖_∞ ≤ (1 − d)‖f‖_∞` for
every vertex `i`, i.e. `‖Δ‖_∞ ≤ 1 − d`, stated for any bound `M` on `|f|`. -/
theorem delta_norm_le {V : Type*} (G : WDigraph V) (c d : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1) (hG : G.Valid c) (f : V → ℝ) (M : ℝ)
    (hf : ∀ v, |f v| ≤ M) (i : V) :
    |Δ G c d f i| ≤ (1 - d) * M := by sorry

end DirectedOpinion.Typical
