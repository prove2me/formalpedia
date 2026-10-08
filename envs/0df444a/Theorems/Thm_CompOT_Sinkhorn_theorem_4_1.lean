-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_theorem_4_1
-- name    : CompOT.Sinkhorn.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:08.868755+00:00
-- url     : https://prove2.me/theorems/87151a2e-a383-4be4-bd97-39df76409e2f
-- title:
--   Theorem 4.1 (Birkhoff–Hopf), p. 440 — d_H(Kv, Kv′) ≤ λ(K) d_H(v, v′) with λ(K) < 1 for a positive matrix K
-- statement:
--   Let $n, m \ge 1$ and let $K \in \mathbb{R}^{n\times m}$ have positive entries. Define
--   $$\eta(K) = \max_{i,j,k,\ell} \frac{K_{i,k}K_{j,\ell}}{K_{j,k}K_{i,\ell}}, \qquad \lambda(K) = \frac{\sqrt{\eta(K)}-1}{\sqrt{\eta(K)}+1}.$$
--   Then $\lambda(K) < 1$, and for all $v, v' \in \mathbb{R}^m$ with positive entries,
--   $$d_{\mathcal H}(Kv, Kv') \le \lambda(K)\, d_{\mathcal H}(v, v'),$$
--   where $d_{\mathcal H}$ is Hilbert's projective metric.
--
--   This is the Birkhoff–Hopf theorem: a matrix with positive entries is a strict contraction of the positive cone for Hilbert's projective metric. It is the engine of the global linear convergence of Sinkhorn's algorithm (Theorem 4.2) and gives a quantitative Perron–Frobenius theorem (Remark 4.13).
--
--   **Formalization Note** The book quotes this theorem (Birkhoff 1957; Samelson et al. 1957) without proof.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.12, Theorem 4.1, p. 440

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

open Matrix

/-- Theorem 4.1 (Birkhoff–Hopf), p. 440: a matrix with positive entries is a strict
contraction for Hilbert's projective metric, with ratio
`λ(K) = (√η(K) − 1)/(√η(K) + 1) < 1`. -/
theorem theorem_4_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v v' : Fin m → ℝ) (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) :
    hilbertMetric (K *ᵥ v) (K *ᵥ v') ≤ lam K * hilbertMetric v v' ∧ lam K < 1 := by sorry

end CompOT.Sinkhorn
