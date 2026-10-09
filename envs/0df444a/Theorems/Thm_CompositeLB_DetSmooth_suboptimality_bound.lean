-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_suboptimality_bound
-- name    : CompositeLB.DetSmooth.suboptimality_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:33:01.274235+00:00
-- url     : https://prove2.me/theorems/f62ebea9-9f71-4d10-b594-de98086bc5ad
-- title:
--   Appendix B.3, p. 15 — explicit 1/(32k²) optimization gap
-- statement:
--   Let $m\ge2$, $k\ge2$, and $a=\sqrt{3/(k+1)}$. Let $v_0,\ldots,v_k$ be orthonormal, with binary component indicators summing to $\lfloor m/2\rfloor$ at each round. If $x\in\mathbb R^d$ is orthogonal to $v_{\lfloor k/2\rfloor},\ldots,v_k$, and $x^*$ minimizes the average hard objective over the unit ball, then
--
--   $$F(x)-F(x^*)\ge\frac1{32k^2}.$$
--
--   This is the quantitative gap for points queried before enough rounds have exposed the hidden directions. The point $x$ need not lie in the unit ball.
--
--   **Formalization Note** $\lfloor k/2\rfloor$ and $\lfloor m/2\rfloor$ are natural-number quotients. The Lean statement uses an explicit attained minimizer instead of an infimum.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Appendix B.3, p. 15, display beginning “F(x) − F(x*)”

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Appendix B.3, p. 15: a point with no coordinate in the last half of
the hidden directions has the paper's explicit optimization gap. -/
theorem suboptimality_bound {m d k : ℕ} (v : ℕ → CompositeLB.DetLip.E d)
    (δ : Fin m → ℕ → ℝ) (a : ℝ) (x xstar : CompositeLB.DetLip.E d)
    (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ)))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (ha : a = Real.sqrt (3 / ((k : ℝ) + 1)))
    (hx : ∀ r : ℕ, k / 2 ≤ r → r ≤ k → inner ℝ x (v r) = 0)
    (hxstar : xstar ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) 1)
    (hmin : ∀ y ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) 1,
      CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) xstar ≤
        CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) y) :
    1 / (32 * (k : ℝ) ^ 2) ≤
      CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x -
        CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) xstar := by sorry

end CompositeLB.DetSmooth
