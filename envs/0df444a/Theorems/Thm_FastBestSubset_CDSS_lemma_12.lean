-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_12
-- name    : FastBestSubset.CDSS.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:37.735335+00:00
-- url     : https://prove2.me/theorems/c1084f79-5224-4da8-a1b0-6b2cd0d4e2fd
-- title:
--   Lemma 12 — a non-spacer step that sets βⱼ to 0 decreases F by at least ((1+2λ₂)/2)(|βⱼᵏ| − √(2λ₀/(1+2λ₂)))²
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$, and let $\{\beta^k\}$ be the iterates of Algorithm 1 with a positive integer $C$. Suppose $\beta^k_j\neq0$ for some coordinate $j$, and that $\beta^{k+1}$ is produced by a non-spacer step which updates coordinate $j$ and sets it to $0$, i.e. $\beta^{k+1}_j=0$. Then
--   $$F(\beta^k)-F(\beta^{k+1})\ge\frac{1+2\lambda_2}{2}\left(|\beta^k_j|-\sqrt{\frac{2\lambda_0}{1+2\lambda_2}}\right)^2 .\tag{38}$$
--
--   The quantitative decrease is what forces a coordinate dropped infinitely often to have limiting magnitude exactly $\sqrt{2\lambda_0/(1+2\lambda_2)}$ in the proof of Theorem 2.
--
--   **Formalization Note** "Step $k\to k+1$ is a non-spacer step updating coordinate $j$" is stated through the algorithm's state after $k$ steps: no spacer step is pending and the cyclic pointer designates $j$.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 12, (38), p. 42 (proof pp. 42–43)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 12 (p. 42): if `βᵏⱼ ≠ 0` and the next step is a non-spacer step that updates
coordinate `j` to `0`, then `F(βᵏ) − F(βᵏ⁺¹) ≥ ((1+2λ₂)/2)(|βᵏⱼ| − √(2λ₀/(1+2λ₂)))²` (38). -/
theorem lemma_12 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ) (k : ℕ) (j : Fin p)
    (hj : iter D C β0 k j ≠ 0)
    (hnonspacer : (stateAt D C β0 k).pending = false)
    (hcoord : coord (stateAt D C β0 k) = j)
    (hzero : iter D C β0 (k + 1) j = 0) :
    (1 + 2 * D.lam2) / 2 * (|iter D C β0 k j| - Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2))) ^ 2 ≤
      F D (iter D C β0 k) - F D (iter D C β0 (k + 1)) := by sorry

end FastBestSubset.CDSS
