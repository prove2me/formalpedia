-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_frobNorm_sq_le
-- name    : CaiCandesShen.ProximalLimit.frobNorm_sq_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:25:21.053802+00:00
-- url     : https://prove2.me/theorems/75759aea-f9fb-4045-8744-f1494de48f31
-- title:
--   Eq. (3.17) — $\|X^\star_\tau\|_F^2 \le \|X_\infty\|_F^2$ for every $\tau>0$
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be constraint functions, let $X_\infty$ be the minimum Frobenius norm solution (3.14) of the nuclear norm problem (1.6), and let $(X^\star_\tau)_{\tau>0}$ be a family such that, for every $\tau>0$, $X^\star_\tau$ solves the proximal problem (3.4). Then for every $\tau>0$,
--   $$\|X^\star_\tau\|_F^2\le\|X_\infty\|_F^2 .$$
--
--   In particular $\|X^\star_\tau\|_F^2$ is bounded uniformly in $\tau$, which is what makes the family $(X^\star_\tau)$ relatively compact in the proof of Theorem 3.1.
--
--   **Formalization Note** The family is a function `Xτ : ℝ → Mat n₁ n₂`; only its values at $\tau>0$ are constrained. Convexity and lower semicontinuity of the $f_i$ are not needed for this step and are omitted.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, proof of Theorem 3.1, Eq. (3.17)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Eq. (3.17), p. 1967: for every `τ > 0`, `‖X⋆_τ‖_F² ≤ ‖X_∞‖_F²`, so `‖X⋆_τ‖_F²` is bounded
uniformly in `τ`. -/
theorem frobNorm_sq_le {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    ∀ τ, 0 < τ → frobNorm (Xτ τ) ^ 2 ≤ frobNorm Xinf ^ 2 := by sorry

end CaiCandesShen.ProximalLimit
