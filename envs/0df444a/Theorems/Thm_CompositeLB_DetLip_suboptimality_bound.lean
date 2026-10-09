-- Prove2me | Theorems.Thm_CompositeLB_DetLip_suboptimality_bound
-- name    : CompositeLB.DetLip.suboptimality_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:24.429416+00:00
-- url     : https://prove2.me/theorems/5055602f-5f64-40cb-bcba-4c94dfdb382c
-- title:
--   Appendix B.1, p. 12: the unrevealed direction forces a suboptimality gap
-- statement:
--   Under the orthonormality, indicator, and normalization assumptions of the hard construction, let $x^*$ minimize $F$ on the unit ball. If $\langle x,v_k\rangle=0$, then
--
--   $$F(x)-F(x^*)\ge\frac{b}{6\sqrt{k}}\ge\frac1{12k}.$$
--
--   This gives the error threshold for a query point that has not revealed the final direction.
--
--   **Formalization Note** The paper obtains $\langle x,v_k\rangle=0$ for iterates produced before round $k$ finishes. The theorem states the numerical bound for any $x\in\mathbb R^d$ with this orthogonality, including points outside the unit ball. The minimum is represented by an explicit feasible minimizer $x^*$.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.1, p. 12, display after 'Therefore, F achieves its minimum'

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Appendix B.1, p. 12: an iterate orthogonal to the unrevealed direction has a fixed gap. -/
theorem suboptimality_bound {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : Fin m → ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (hb : b = 1 / Real.sqrt ((k + 1 : ℕ) : ℝ))
    (x xstar : E d)
    (hx : inner ℝ x (v k) = 0)
    (hstar_mem : xstar ∈ Metric.closedBall (0 : E d) 1)
    (hstar_min : ∀ y ∈ Metric.closedBall (0 : E d) 1,
      avgF (fun i => hardF b k v (δ i)) xstar ≤
        avgF (fun i => hardF b k v (δ i)) y) :
    b / (6 * Real.sqrt (k : ℝ)) ≤
        avgF (fun i => hardF b k v (δ i)) x -
          avgF (fun i => hardF b k v (δ i)) xstar ∧
      1 / (12 * (k : ℝ)) ≤ b / (6 * Real.sqrt (k : ℝ)) := by sorry

end CompositeLB.DetLip
