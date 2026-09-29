-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_nuclearNorm_tendsto
-- name    : CaiCandesShen.ProximalLimit.nuclearNorm_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:25:51.946988+00:00
-- url     : https://prove2.me/theorems/b142e37f-add2-442c-9637-9c0b6eb870e5
-- title:
--   Proof of Theorem 3.1 — $\lim_{\tau\to\infty}\|X^\star_\tau\|_* = \|X_\infty\|_*$
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be constraint functions, let $X_\infty$ be the minimum Frobenius norm solution (3.14) of the nuclear norm problem (1.6), and let $(X^\star_\tau)_{\tau>0}$ be a family such that, for every $\tau>0$, $X^\star_\tau$ solves the proximal problem (3.4). Then, as $\tau\to\infty$ through the real numbers,
--   $$\lim_{\tau\to\infty}\|X^\star_\tau\|_*=\|X_\infty\|_* .$$
--
--   The nuclear norms of the proximal solutions thus converge to the optimal value of (1.6); this is what shows that every limit point of $X^\star_\tau$ solves (1.6).
--
--   **Formalization Note** The limit is taken along `Filter.atTop` on $\mathbb R$; only the values of the family at $\tau>0$ are constrained, which is enough for a limit at $+\infty$. The paper states the matching $\limsup$ and $\liminf$ bounds and concludes the limit; the limit is formalized directly. Convexity and lower semicontinuity of the $f_i$ are not needed for this step and are omitted.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, proof of Theorem 3.1, display after Eq. (3.17) and the sentence "An immediate consequence is …"

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967 (display after (3.17)): `lim_{τ→∞} ‖X⋆_τ‖_* = ‖X_∞‖_*`. -/
theorem nuclearNorm_tendsto {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => nuclearNorm (Xτ τ)) atTop (𝓝 (nuclearNorm Xinf)) := by sorry

end CaiCandesShen.ProximalLimit
