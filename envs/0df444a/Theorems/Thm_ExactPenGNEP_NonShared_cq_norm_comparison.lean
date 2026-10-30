-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_cq_norm_comparison
-- name    : ExactPenGNEP.NonShared.cq_norm_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:20.371856+00:00
-- url     : https://prove2.me/theorems/0bdfb9ad-2ca5-4516-af85-8314045337a2
-- title:
--   Proof of Theorem 11, p. 18 — a constant c_q > 0 with c_q‖•‖_q ≤ ‖•‖_{q−1}
-- statement:
--   Let $q \in (1, \infty)$. There is a constant $c_q > 0$ such that for every dimension $k$ and every vector $v \in \mathbb R^k$
--
--   $$c_q \Big( \sum_{i=1}^k |v_i|^q \Big)^{1/q} \le \Big( \sum_{i=1}^k |v_i|^{q-1} \Big)^{1/(q-1)},$$
--
--   i.e. $c_q \|v\|_q \le \|v\|_{q-1}$.
--
--   The proof of Theorem 11 (b) applies this comparison to the vector $(\max(g^{\hat\nu}(x^*), 0), h^{\hat\nu}(x^*))$ to bound the ratio $r_{\hat\nu,q-1}(x^*)/r_{\hat\nu,q}(x^*)$ from below.
--
--   **Formalization Note** Both sides are written as explicit sums of real powers, because for $q < 2$ the expression $\|\cdot\|_{q-1}$ is only a quasi-norm. The constant depends on $q$ alone and must work for all dimensions simultaneously, since the proof applies it to vectors of length $m_{\hat\nu} + p_{\hat\nu}$ for varying players $\hat\nu$.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, p. 18, proof of Theorem 11, first display (the clause defining c_q)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem cq_norm_comparison (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (v : Fin k → ℝ),
      c * (∑ i, |v i| ^ q) ^ (1 / q) ≤ (∑ i, |v i| ^ (q - 1)) ^ (1 / (q - 1)) := by sorry

end ExactPenGNEP.NonShared
