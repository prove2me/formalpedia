-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_Fsum_eq
-- name    : CompositeLB.DetSmooth.Fsum_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:42.083672+00:00
-- url     : https://prove2.me/theorems/ef9ca83c-31db-462d-b46d-3c71d322ac73
-- title:
--   Appendix B.3, p. 14 — the full and truncated averages agree at hidden-direction-orthogonal points
-- statement:
--   Suppose $m\ge2$, $k\ge1$, $v_0,\ldots,v_k$ are orthonormal, each $\delta_{i,r}$ is binary, and exactly $\lfloor m/2\rfloor$ components have $\delta_{i,r}=1$ for each $1\le r\le k$. The average of the hard components equals $F^{k+1}$ everywhere. If $1\le q\le k$ and $x$ is orthogonal to $v_q,\ldots,v_k$, then
--
--   $$F^q(x)=F^{k+1}(x)=F(x).$$
--
--   This equality transfers the minimum of an early truncated quadratic into a lower bound for the final objective at points that have not revealed later directions.
--
--   **Formalization Note** Orthogonality to $v_q,\ldots,v_k$ expresses the paper's span condition. The indicator sum uses natural-number division $m/2=\lfloor m/2\rfloor$.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Appendix B.3, p. 14, display after the definition of F^t and paragraph beginning “Then if d”

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Appendix B.3, p. 14: the aggregate hard function is `F^(k+1)`, and an
iterate orthogonal to all directions from round `q` onward sees `F^q`. -/
theorem Fsum_eq {m d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (δ : Fin m → ℕ → ℝ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ)))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ)) :
    (∀ x : CompositeLB.DetLip.E d, CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x = Fsum m a v (k + 1) x) ∧
    (∀ q : ℕ, 1 ≤ q → q ≤ k → ∀ x : CompositeLB.DetLip.E d,
      (∀ r : ℕ, q ≤ r → r ≤ k → inner ℝ x (v r) = 0) →
      Fsum m a v q x = CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x) := by sorry

end CompositeLB.DetSmooth
