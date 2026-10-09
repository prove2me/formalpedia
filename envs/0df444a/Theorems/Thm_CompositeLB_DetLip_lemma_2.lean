-- Prove2me | Theorems.Thm_CompositeLB_DetLip_lemma_2
-- name    : CompositeLB.DetLip.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:26.380054+00:00
-- url     : https://prove2.me/theorems/17e7c79a-a245-434b-bec5-696100467140
-- title:
--   Lemma 2, p. 12: subgradients of the truncated hard component remain valid
-- statement:
--   Let $1\le t\le k$, let $v_0,\ldots,v_k$ be orthonormal, and let the indicators $\delta_r$ take values in $\{0,1\}$. Suppose component $i$ is queried in round $t$, so $\delta_t=0$. If the orthogonal projection $x^v=\sum_{r=0}^k\langle x,v_r\rangle v_r$ lies in $\operatorname{span}\{v_0,\ldots,v_{t-1}\}$, then
--
--   $$\partial f_i^t(x)\subseteq\partial f_i(x).$$
--
--   This certifies that a subgradient returned from the truncated component can be returned by the final component.
--
--   **Formalization Note** The span condition is represented by $\langle x,v_r\rangle=0$ for $t\le r\le k$, equivalent under orthonormality. Rounds begin at one. Subgradients use the published global inequality, which includes every subgradient at an absolute-value kink; the printed proof's choice $\operatorname{sign}(0)=0$ alone does not describe them all.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Lemma 2, p. 12

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Lemma 2, p. 12: a truncated subgradient is a subgradient of the completed function. -/
theorem lemma_2 {d k : ℕ} (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ r, δ r = 0 ∨ δ r = 1)
    (t : ℕ) (ht : 1 ≤ t) (htk : t ≤ k) (hδt : δ t = 0)
    (x : E d)
    (hx : ∀ r, t ≤ r → r ≤ k → inner ℝ x (v r) = 0) :
    ∀ g : E d,
      ShorNonsmooth.AlmostDiff.IsSubgradient (hardFt b k v δ t) x g →
        ShorNonsmooth.AlmostDiff.IsSubgradient (hardF b k v δ) x g := by sorry

end CompositeLB.DetLip
