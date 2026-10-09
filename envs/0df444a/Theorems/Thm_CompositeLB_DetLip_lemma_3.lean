-- Prove2me | Theorems.Thm_CompositeLB_DetLip_lemma_3
-- name    : CompositeLB.DetLip.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:48.534633+00:00
-- url     : https://prove2.me/theorems/e07ea10b-966c-442d-99f5-c3092a82204e
-- title:
--   Lemma 3, pp. 12–13: truncated and final components have the same prox points
-- statement:
--   Let $1\le t\le k$, let $v_0,\ldots,v_k$ be orthonormal, and let the indicators $\delta_r$ take values in $\{0,1\}$. Suppose $\delta_t=0$ and $x^v=\sum_{r=0}^k\langle x,v_r\rangle v_r$ belongs to $\operatorname{span}\{v_0,\ldots,v_{t-1}\}$. For every $\beta>0$, the truncated and final component have exactly the same proximal points:
--
--   $$\operatorname{prox}_{f_i^t}(x,\beta)=\operatorname{prox}_{f_i}(x,\beta).$$
--
--   This is the proximal-response consistency needed for the resisting oracle.
--
--   **Formalization Note** Proximal minimizers are taken over the unit ball, as equation (3) requires; the printed proof computes an unconstrained argmin. Equality is encoded as equivalence of minimizer predicates for every candidate point. The displayed expansion (14) prints $1/\sqrt{k}$ where equation (6) has $1/(2\sqrt{k})$; the formal statement follows equation (6).
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Lemma 3, pp. 12–13

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Lemma 3, pp. 12–13: the truncated and completed constrained proximal points agree. -/
theorem lemma_3 {d k : ℕ} (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ r, δ r = 0 ∨ δ r = 1)
    (t : ℕ) (ht : 1 ≤ t) (htk : t ≤ k) (hδt : δ t = 0)
    (x : E d)
    (hx : ∀ r, t ≤ r → r ≤ k → inner ℝ x (v r) = 0) :
    ∀ β : ℝ, 0 < β → ∀ u : E d,
      IsProx (hardFt b k v δ t) (Metric.closedBall (0 : E d) 1) β x u ↔
        IsProx (hardF b k v δ) (Metric.closedBall (0 : E d) 1) β x u := by sorry

end CompositeLB.DetLip
