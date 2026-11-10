-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_lemma_3_5
-- name    : AgnosticImitate.Reduction.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:57.634842+00:00
-- url     : https://prove2.me/theorems/db57c3cf-50cb-442e-b67f-05b39b4bd025
-- title:
--   Lemma 3.5 — if ∂ℓ ∘ k is β-Lipschitz, the FTL regret is at most 2β Σ_t w_t²/W_t
-- statement:
--   In the setting of Lemma 3.4, if $\partial\ell\circ k$ is $\beta$-Lipschitz on $[\pm1]$, then
--   $$\sum_{t=1}^TW_t\,D_\ell(\bar p_t,k(\bar p_{t-1}))\le2\beta\sum_{t=1}^T\frac{w_t^2}{W_t}.$$
--   (The paper states $O(\beta\sum_tw_t^2/W_t)$; the constant $2$ is the one its proof gives.)
--
--   Differences from the source:
--   - encoding: a loss ℓ : {±1} × A → ℝ → ℓ : ℝ → A → ℝ, used only at y = 1 and y = −1 (expLoss); reason: the values at other y never enter
--   - encoding: k_ℓ(p) ∈ argmin_a ℓ(p, a), the best-response function → a given selection k with IsBestResponse ℓ k (ℓ(p, k(p)) ≤ ℓ(p, a) for all p ∈ [−1, 1] and all a); reason: the paper's k_ℓ is a chosen selection; a best response need not exist in general, so it is assumed given
--   - encoding: ∂ℓ ∘ k_ℓ is β-Lipschitz → |∂ℓ(k(x)) − ∂ℓ(k(y))| ≤ β|x − y| for x, y ∈ [−1, 1]; reason: k_ℓ is a best response on [±1], where all averages lie
--   - generalization: the bound O(β Σ_t w_t²/W_t) → the explicit bound 2β Σ_t w_t²/W_t; reason: the proof (p. 41) gives the constant 2; an explicit constant implies the O-bound
--   - generalization: p̄_t = (w_1p_1 + ⋯ + w_tp_t)/W_t, which presupposes W_t > 0 (w_1 > 0) → no positivity of the weights beyond w_t ≥ 0; Lean's x/0 = 0 gives p̄_t = 0 (and w_t²/W_t = 0) while W_t = 0; reason: covers weight sequences with leading zeros, where the source's averages are undefined; when w_1 > 0 it is the source's statement
--   - encoding: weights w_1, …, w_T and means p_1, …, p_T → sequences w, p : ℕ → ℝ with hypotheses on t ∈ {1, …, T} (prefixW, wavg); reason: only the entries 1, …, T enter
--   - generalization: a positive number T of FTL rounds → T may also be zero; reason: all sums are empty and both sides are zero; in Lemma 3.4 the supplied best-response function supplies an action k(0)
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Lemma 3.5, p. 20 (PDF 22); constant 2 from its proof, p. 41 (PDF 43)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Losses

namespace AgnosticImitate.Reduction

/-- Lemma 3.5 (p. 20, PDF 22), with the constant `2` of its proof (p. 41, PDF 43). In the
setting of Lemma 3.4, if `∂ℓ ∘ k` is `β`-Lipschitz on `[±1]`, then
`Σ_t W_t D_ℓ(p̄_t, k(p̄_{t-1})) ≤ 2 β Σ_t w_t² / W_t`. -/
theorem lemma_3_5 {A : Type*} (ℓ : ℝ → A → ℝ) (k : ℝ → A) (hk : IsBestResponse ℓ k)
    (T : ℕ) (w p : ℕ → ℝ) (hw : ∀ t ∈ Finset.Icc 1 T, 0 ≤ w t)
    (hp : ∀ t ∈ Finset.Icc 1 T, p t ∈ Set.Icc (-1 : ℝ) 1) (β : ℝ)
    (hβ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |discDeriv ℓ (k x) - discDeriv ℓ (k y)| ≤ β * |x - y|) :
    ∑ t ∈ Finset.Icc 1 T, prefixW w t * divergence ℓ (wavg w p t) (k (wavg w p (t - 1))) ≤
      2 * β * ∑ t ∈ Finset.Icc 1 T, w t ^ 2 / prefixW w t := by sorry

end AgnosticImitate.Reduction
