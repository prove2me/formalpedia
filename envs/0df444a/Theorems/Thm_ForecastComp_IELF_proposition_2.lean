-- Prove2me | Theorems.Thm_ForecastComp_IELF_proposition_2
-- name    : ForecastComp.IELF.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:31.448991+00:00
-- url     : https://prove2.me/theorems/ea3d7e23-1e1f-4e38-8c32-b849f3a59581
-- title:
--   Proposition 2, p. 11 — ELF selection probability under a joint law θ
-- statement:
--   Let $n\ge2$, $m\ge1$, let $\theta$ be any joint probability law of the outcomes $X\in\{0,1\}^m$ (not necessarily independent), and let $y_1,\dots,y_n\in[0,1]^m$. The multi-event ELF mechanism (2), which selects $i$ with probability $g_i=\frac1m\sum_k f_{i,k}$, satisfies
--   $$\Pr_{X\sim\theta}\big(M_{\text{ELF}^R}(y_1,\dots,y_n,X)=i\big)=\frac1n+\frac1n\Big(R(y_i,\theta)-\frac1{n-1}\sum_{j\ne i}R(y_j,\theta)\Big),$$
--   where $R(y_i,\theta)=\mathbb E_{X\sim\theta}\frac1m\sum_k R(y_{i,k},X_k)$.
--
--   Applied to a single event, it says that the expected ELF lottery of a forecaster is an affine function of the forecasters' expected scores, which drives the proof of Theorem 7.
--
--   **Formalization Note** The identity is algebraic and holds for every real-valued $R$; no boundedness or properness of $R$ is assumed (a disclosed strengthening).
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 11, Proposition 2 (proof p. 26, Appendix H); eq. (2), p. 9

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

open MeasureTheory

/-- Proposition 2, p. 11 (proof p. 26): for any joint law `θ` of the outcomes, multi-event ELF
selects forecaster `i` with probability
`1/n + (1/n)(R(y_i,θ) − (1/(n−1)) Σ_{j≠i} R(y_j,θ))`. -/
theorem proposition_2 {m n : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (R : ℝ → Bool → ℝ)
    (θ : Measure (Fin m → Bool)) [IsProbabilityMeasure θ]
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k, y j k ∈ Set.Icc (0:ℝ) 1) (i : Fin n) :
    ∫ x, elfMultiProb R y x i ∂θ =
      1 / (n:ℝ) + 1 / (n:ℝ) * (avgScoreJoint R θ (y i) -
        1 / ((n:ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, avgScoreJoint R θ (y j)) := by sorry

end ForecastComp.IELF
