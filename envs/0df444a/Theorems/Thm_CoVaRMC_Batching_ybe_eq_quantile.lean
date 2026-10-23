-- Prove2me | Theorems.Thm_CoVaRMC_Batching_ybe_eq_quantile
-- name    : CoVaRMC.Batching.ybe_eq_quantile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:51.271689+00:00
-- url     : https://prove2.me/theorems/c848bc47-aa99-418d-9598-dc1e5e604498
-- title:
--   p. 8 — Ŷ^BE = F̂^{−1}_k(β), the β-inverse of the empirical distribution function of Ŷ_1, …, Ŷ_k
-- statement:
--   Let $\hat Y_1, \dots, \hat Y_k$ ($k \ge 1$) be the batch values of the batching procedure, $\hat F_k(y) = \frac1k \sum_{i=1}^k I\{\hat Y_i \le y\}$ their empirical distribution function, and $\hat F_k^{-1}(z) = \inf\{y \in \mathbb R : \hat F_k(y) \ge z\}$. For every $\beta \in (0,1)$, the batching estimator $\hat Y^{\mathrm{BE}} = \hat Y_{(\lceil \beta k\rceil)}$ satisfies
--   $$\hat Y^{\mathrm{BE}} = \hat F_k^{-1}(\beta).$$
--
--   The identity converts statements about the estimator into statements about the empirical distribution function, which is how both the consistency and the normality proofs proceed.
--
--   **Formalization Note.** The identity is deterministic: it holds for every outcome $\omega$ and every sample array, and the batch size $m$ plays no role. For $\beta \in (0,1)$ the set $\{y : \hat F_k(y) \ge \beta\}$ is nonempty and bounded below, so the real infimum is a genuine minimum.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 8, 'we have Ŷ^BE = F̂^{−1}_k(β)'

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- p. 8: the batching estimator is the `β`-inverse of the empirical distribution function,
`Ŷ^BE = F̂_k^{-1}(β) = inf {y ∈ ℝ : F̂_k(y) ≥ β}`. -/
theorem ybe_eq_quantile {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (k m : ℕ) (hk : 0 < k) (ω : Ω) :
    YBE S α β k m ω = sInf {y : ℝ | β ≤ FkHat S α k m y ω} := by sorry

end CoVaRMC.Batching
