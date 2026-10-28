-- Prove2me | Theorems.Thm_ForecastComp_IELF_eq_9
-- name    : ForecastComp.IELF.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:31.689706+00:00
-- url     : https://prove2.me/theorems/ea43eb3a-58ac-4cc3-b875-5e596116431f
-- title:
--   Eq. (9), p. 35 — expected event wins differ by m(R(y_i,θ) − R(y_j,θ))/(n−1)
-- statement:
--   Let $n\ge2$, let the outcomes of $m$ events be independent with $\Pr(X_k=1)=\theta_k\in[0,1]$, and let $Z_i$ be the number of event lotteries of I-ELF won by forecaster $i$. For any reports $y$ and any two forecasters $i\ne j$,
--   $$\mathbb E_{X\sim\theta}[Z_i]-\mathbb E_{X\sim\theta}[Z_j]=\frac{m\big(R(y_i,\theta)-R(y_j,\theta)\big)}{n-1},$$
--   and consequently, whenever $R(y_i,\theta)-R(y_j,\theta)\ge\Delta$,
--   $$\mathbb E_{X\sim\theta}[Z_i]-\mathbb E_{X\sim\theta}[Z_j]\ge\frac{m\Delta}{n-1}.$$
--
--   The more accurate forecaster wins more event lotteries in expectation, by an amount growing linearly in $m$.
--
--   **Formalization Note** The identity holds for every real-valued $R$ and all real reports (it only uses that each ELF lottery sums to one); no bound on $R$ is assumed.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 35, eq. (9), proof of Theorem 7 (Appendix M)

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Eq. (9), p. 35: under independent outcomes with marginals `θ`, the expected numbers of event
wins of forecasters `i` and `j` differ by `m (R(y_i,θ) − R(y_j,θ))/(n−1)`; in particular the
difference is at least `mΔ/(n−1)` when `R(y_i,θ) − R(y_j,θ) ≥ Δ`. -/
theorem eq_9 {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (θ : Fin m → ℝ) (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) (hij : i ≠ j) :
    expWins R θ y i - expWins R θ y j =
        (m:ℝ) * (avgScore R θ (y i) - avgScore R θ (y j)) / ((n:ℝ) - 1) ∧
    ∀ Δ : ℝ, Δ ≤ avgScore R θ (y i) - avgScore R θ (y j) →
      (m:ℝ) * Δ / ((n:ℝ) - 1) ≤ expWins R θ y i - expWins R θ y j := by sorry

end ForecastComp.IELF
