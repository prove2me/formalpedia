-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_subsequence_limit_eq
-- name    : CaiCandesShen.ProximalLimit.subsequence_limit_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:26:59.391088+00:00
-- url     : https://prove2.me/theorems/5c8ccdf1-14b8-4ef7-ac57-b297649bd5e5
-- title:
--   Proof of Theorem 3.1 — every convergent subsequence $X^\star_{\tau_k}$ converges to $X_\infty$
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be convex and lower semicontinuous, let $X_\infty$ be the minimum Frobenius norm solution (3.14) of the nuclear norm problem (1.6), and let $(X^\star_\tau)_{\tau>0}$ be a family such that, for every $\tau>0$, $X^\star_\tau$ solves the proximal problem (3.4). Let $(\tau_k)_{k\ge 1}$ be real numbers with $\tau_k\to\infty$, and suppose that $X^\star_{\tau_k}\to X_c$ as $k\to\infty$. Then
--   $$X_c=X_\infty .$$
--
--   Together with the uniform bound (3.17), which makes the family $(X^\star_\tau)$ bounded, this identifies every cluster point of $X^\star_\tau$ as $\tau\to\infty$ and reduces Theorem 3.1 to it.
--
--   **Formalization Note** A "subsequence" is any sequence `t : ℕ → ℝ` tending to $+\infty$, and convergence of matrices is in Mathlib's entrywise topology on `Matrix`, which on this finite-dimensional space is the topology of $\|\cdot\|_F$. The paper's text at this point says "$X_c$ is a solution to (1.1)"; the problem meant is (1.6), the constrained problem of Theorem 3.1, and that is what is formalized.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, proof of Theorem 3.1, from "Thus, we would prove the theorem if …" to the end of the proof

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967: if `τ_k → ∞` and `X⋆_{τ_k} → X_c`, then `X_c = X_∞`. -/
theorem subsequence_limit_eq {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ))
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (Xc : Mat n₁ n₂)
    (hXc : Tendsto (fun k => Xτ (t k)) atTop (𝓝 Xc)) :
    Xc = Xinf := by sorry

end CaiCandesShen.ProximalLimit
