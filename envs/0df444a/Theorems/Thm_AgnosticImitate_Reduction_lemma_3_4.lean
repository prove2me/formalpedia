-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_lemma_3_4
-- name    : AgnosticImitate.Reduction.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:53.624997+00:00
-- url     : https://prove2.me/theorems/9e4130ab-0918-42f3-b58e-ff5999c2ea64
-- title:
--   Lemma 3.4 — exact regret of weighted Follow the Leader: regret = Σ_t W_t D_ℓ(p̄_t, k(p̄_{t−1}))
-- statement:
--   Let $\ell$ be a loss with best-response function $k$, weights $w_1,\dots,w_T\ge0$ and distribution means $p_1,\dots,p_T\in[\pm1]$; let $W_t=w_1+\dots+w_t$ and $\bar p_t=(w_1p_1+\dots+w_tp_t)/W_t$, $\bar p_0=0$. Then $\min_{a\in A}\sum_{t=1}^Tw_t\,\ell(p_t,a)$ is attained, and Follow the Leader, which plays $k(\bar p_{t-1})$ in round $t$, satisfies
--   $$\sum_{t=1}^Tw_t\,\ell(p_t,k(\bar p_{t-1}))-\min_{a\in A}\sum_{t=1}^Tw_t\,\ell(p_t,a)=\sum_{t=1}^TW_t\,D_\ell(\bar p_t,k(\bar p_{t-1})).$$
--
--   Differences from the source:
--   - encoding: a loss ℓ : {±1} × A → ℝ → ℓ : ℝ → A → ℝ, used only at y = 1 and y = −1 (expLoss); reason: the values at other y never enter
--   - encoding: k_ℓ(p) ∈ argmin_a ℓ(p, a), the best-response function → a given selection k with IsBestResponse ℓ k (ℓ(p, k(p)) ≤ ℓ(p, a) for all p ∈ [−1, 1] and all a); reason: the paper's k_ℓ is a chosen selection; a best response need not exist in general, so it is assumed given
--   - encoding: min_{a∈A} Σ_t w_t ℓ(p_t, a) → ∃ a₀ with Σ_t w_t ℓ(p_t, a₀) ≤ Σ_t w_t ℓ(p_t, a) for all a, and the identity with a₀; reason: the printed min presupposes attainment (it is attained at k(p̄_T)); stating the minimizer avoids an unattained infimum
--   - generalization: p̄_t = (w_1p_1 + ⋯ + w_tp_t)/W_t, which presupposes W_t > 0 (w_1 > 0) → no positivity of the weights beyond w_t ≥ 0; Lean's x/0 = 0 gives p̄_t = 0 (and w_t²/W_t = 0) while W_t = 0; reason: covers weight sequences with leading zeros, where the source's averages are undefined; when w_1 > 0 it is the source's statement
--   - encoding: weights w_1, …, w_T and means p_1, …, p_T → sequences w, p : ℕ → ℝ with hypotheses on t ∈ {1, …, T} (prefixW, wavg); reason: only the entries 1, …, T enter
--   - generalization: a positive number T of FTL rounds → T may also be zero; reason: all sums are empty and both sides are zero; in Lemma 3.4 the supplied best-response function supplies an action k(0)
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Lemma 3.4, p. 20 (PDF 22); proofs pp. 40–41 (PDF 42–43)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Losses

namespace AgnosticImitate.Reduction

/-- Lemma 3.4 (Follow the Leader's Regret, p. 20, PDF 22). For weights `w_t ≥ 0` and means
`p_1, …, p_T ∈ [±1]`, with `W_t = w_1 + ⋯ + w_t` and `p̄_t = (w_1 p_1 + ⋯ + w_t p_t)/W_t`
(`p̄_0 = 0`), the minimum over actions of `Σ_t w_t ℓ(p_t, a)` is attained, and Follow the Leader,
which plays `k(p̄_{t-1})` in round `t`, has regret exactly
`Σ_t w_t ℓ(p_t, k(p̄_{t-1})) - min_a Σ_t w_t ℓ(p_t, a) = Σ_t W_t D_ℓ(p̄_t, k(p̄_{t-1}))`. -/
theorem lemma_3_4 {A : Type*} (ℓ : ℝ → A → ℝ) (k : ℝ → A) (hk : IsBestResponse ℓ k)
    (T : ℕ) (w p : ℕ → ℝ) (hw : ∀ t ∈ Finset.Icc 1 T, 0 ≤ w t)
    (hp : ∀ t ∈ Finset.Icc 1 T, p t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ a₀ : A,
      (∀ a : A, ∑ t ∈ Finset.Icc 1 T, w t * expLoss ℓ (p t) a₀ ≤
        ∑ t ∈ Finset.Icc 1 T, w t * expLoss ℓ (p t) a) ∧
      (∑ t ∈ Finset.Icc 1 T, w t * expLoss ℓ (p t) (k (wavg w p (t - 1)))) -
          ∑ t ∈ Finset.Icc 1 T, w t * expLoss ℓ (p t) a₀ =
        ∑ t ∈ Finset.Icc 1 T, prefixW w t * divergence ℓ (wavg w p t) (k (wavg w p (t - 1))) := by sorry

end AgnosticImitate.Reduction
