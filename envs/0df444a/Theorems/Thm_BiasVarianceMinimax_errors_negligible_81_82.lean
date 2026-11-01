-- Prove2me | Theorems.Thm_BiasVarianceMinimax_errors_negligible_81_82
-- name    : BiasVarianceMinimax.errors_negligible_81_82
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:33.976723+00:00
-- url     : https://prove2.me/theorems/dab8f473-c2cf-45ab-8e1f-9d62cf801b74
-- title:
--   (81), (82) — the error terms are negligible
-- statement:
--   Let $w^*_{j,n}$ be the weights $W^*(a)$ with $a_n$ optimal for (24) for all large $n$, and let $r(j)\to 0$ as $j\to\infty$. Then
--
--   $$\sum_{j=1}^n\frac{w^*_{j,n}\,r(j)}{(j+n_0)^{\alpha q_1}}=o\Big(\sum_{j=1}^n\frac{w^*_{j,n}}{(j+n_0)^{\alpha q_1}}\Big),\qquad \sum_{j=1}^n (j+n_0)^{2\alpha q_2}(w^*_{j,n})^2\,r(j)=o\Big(\sum_{j=1}^n (j+n_0)^{2\alpha q_2}(w^*_{j,n})^2\Big).$$
--
--   These are what let the higher-order terms of an arbitrary model in $\Theta$ be dropped.
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - encoding: the o(1) of (81), (82) → a sequence r(j) → 0 indexed by the run, the same for all n; reason: the o(1) comes from the δⱼ of run j, which do not depend on n
--   - reading: w∗ at each n → a selection optimal for all large n; reason: (24) can be empty at finite n
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (81), (82), p.56; pp.56–57

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

open Filter Topology Asymptotics

namespace BiasVarianceMinimax

/-- **The error terms are negligible.** Lam, Zhang & Zhang, arXiv:1902.04673v1, (81), (82), p.56, with
the argument on pp.56–57.

For `W∗(a)` with `a` optimal for large `n`, and every sequence `r(j) → 0`, indexed by the run and the
same for all `n`, the perturbed sums differ from the main sums by a lower-order term.

**Formalization Note.** `r(j)` is the `o(1)` of (81), (82). The weights are signed, so `r` is not
bounded termwise against the main sum. With the shift `n₀`. -/
theorem errors_negligible_81_82 (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K) (n₀ : ℕ)
    (a : ℕ → ℝ) (ha : ∀ᶠ n in atTop, IsOptimal q₁ q₂ K n₀ n (a n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    (fun n : ℕ => ∑ j : Fin n, weightStar q₁ q₂ n₀ a n j * r j
        / runPoint n₀ j ^ (alpha q₁ q₂ * q₁))
      =o[atTop] (fun n : ℕ => muSum q₁ q₂ n₀ n (weightStar q₁ q₂ n₀ a n)) ∧
    (fun n : ℕ => ∑ j : Fin n, runPoint n₀ j ^ (2 * alpha q₁ q₂ * q₂)
        * weightStar q₁ q₂ n₀ a n j ^ 2 * r j)
      =o[atTop] (fun n : ℕ => sigmaSum q₁ q₂ n₀ n (weightStar q₁ q₂ n₀ a n)) := by sorry

end BiasVarianceMinimax
