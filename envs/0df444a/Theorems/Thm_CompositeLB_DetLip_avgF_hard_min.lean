-- Prove2me | Theorems.Thm_CompositeLB_DetLip_avgF_hard_min
-- name    : CompositeLB.DetLip.avgF_hard_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:37:20.693301+00:00
-- url     : https://prove2.me/theorems/db6fbf64-ccb8-48d4-9b74-b5c0911245eb
-- title:
--   Appendix B.1, p. 12: the average hard function is nonnegative and attains zero
-- statement:
--   Let $m\ge2$ and $k\ge1$. Let $v_0,\ldots,v_k$ be orthonormal, and let $\delta_{i,r}\in\{0,1\}$ satisfy $\sum_i\delta_{i,r}=\lfloor m/2\rfloor$ for every $1\le r\le k$. Put $b=1/\sqrt{k+1}$, let $f_i$ be equation (6), and set $x_b=b\sum_{r=0}^k v_r$. Their average is
--
--   $$F(x)=\frac1{\sqrt2}|b-\langle x,v_0\rangle|+\frac{\lfloor m/2\rfloor}{2m\sqrt{k}}\sum_{r=1}^k|\langle x,v_{r-1}\rangle-\langle x,v_r\rangle|.$$
--
--   For every $x$, $F(x)\ge0$; moreover $F(x_b)=0$ and $\|x_b\|=1$. Thus the hard objective has an attained minimum on the unit ball.
--
--   **Formalization Note** `m / 2` is natural-number division, representing $\lfloor m/2\rfloor$. The component indices are `Fin m` and correspond to the paper's $1,\ldots,m$.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.1, p. 12, displays from F(x) through ‖x_b‖ = 1

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Appendix B.1, p. 12: the averaged hard function and its attained minimum. -/
theorem avgF_hard_min {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : Fin m → ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (hb : b = 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    let f : Fin m → E d → ℝ := fun i => hardF b k v (δ i)
    let xb : E d := b • ∑ r ∈ Finset.range (k + 1), v r
    (∀ x : E d,
      avgF f x = 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
        (((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ))) *
          ∑ r ∈ Finset.Icc 1 k,
            |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|) ∧
    (∀ x : E d, 0 ≤ avgF f x) ∧ avgF f xb = 0 ∧ ‖xb‖ = 1 := by sorry

end CompositeLB.DetLip
