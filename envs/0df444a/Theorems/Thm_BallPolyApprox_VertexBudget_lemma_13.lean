-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_13
-- name    : BallPolyApprox.VertexBudget.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:32.850884+00:00
-- url     : https://prove2.me/theorems/899a6fdb-4d44-4e6a-8425-9321bcba6406
-- title:
--   Lemma 13 — the median sign $\sigma_k$ is orthogonal to affine functions of $\Lambda$, and $\mathbb E(\Lambda_i\Lambda_j\sigma_k)=\beta_m\mathbb E(\Lambda_i\Lambda_j)$
-- statement:
--   Let $m\ge1$, $k=m+1$, $\Lambda\sim\mathrm{Dirichlet}_k(1,\dots,1)$, $Q_k=\sum_i\Lambda_i^2$, $\mu_k=\mathrm{med}(Q_k)$ and $\sigma_k=\mathrm{sign}(\mu_k-Q_k)$. For every $1\le i\le k$ and every $j\ne i$,
--   $$\mathbb E\sigma_k=0,\qquad\mathbb E(\Lambda_i\sigma_k)=0\quad(30),$$
--   $$\mathbb E(\Lambda_i\Lambda_j\sigma_k)=\beta_m\mathbb E(\Lambda_i\Lambda_j),\qquad\beta_m:=\frac{m+2}m\mathbb E|Q_{m+1}-\mu_{m+1}|=\frac{k+1}{k-1}\mathbb E|Q_k-\mu_k|\quad(31).$$
--
--   Differences from the source:
--   - encoding: indices 1 ≤ i ≤ k, j ≠ i, with k = m + 1 → i, j : Fin (m + 1) with i ≠ j; reason: zero-based indexing of the same k = m + 1 coordinates; no instance changes
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 13, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 13 (p. 15, PDF 17): let `m ≥ 1`, `k = m + 1`, `Λ ~ Dirichlet_k(1, …, 1)`,
`Q_k = Σ Λ_i²`, `μ_k = med(Q_k)` and `σ_k = sign(μ_k − Q_k)`. For every `1 ≤ i ≤ k` and every
`j ≠ i`: `E σ_k = 0`, `E(Λ_i σ_k) = 0` (30), and `E(Λ_i Λ_j σ_k) = β_m E(Λ_i Λ_j)` with
`β_m = ((m+2)/m) E|Q_{m+1} − μ_{m+1}| = ((k+1)/(k−1)) E|Q_k − μ_k|` (31). -/
theorem lemma_13 (m : ℕ) (hm : 1 ≤ m) :
    ∫ w, medianSign (m + 1) w ∂dirichletOnes (m + 1) = 0 ∧
    (∀ i : Fin (m + 1), ∫ w, w i * medianSign (m + 1) w ∂dirichletOnes (m + 1) = 0) ∧
    (∀ i j : Fin (m + 1), i ≠ j →
      ∫ w, w i * w j * medianSign (m + 1) w ∂dirichletOnes (m + 1) =
        betaM m * ∫ w, w i * w j ∂dirichletOnes (m + 1)) ∧
    betaM m = (((m + 1 : ℕ) : ℝ) + 1) / (((m + 1 : ℕ) : ℝ) - 1) *
      ∫ w, |greenwood w - greenwoodMedian (m + 1)| ∂dirichletOnes (m + 1) := by sorry

end BallPolyApprox.VertexBudget
