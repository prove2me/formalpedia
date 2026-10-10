-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_lemma_3_1
-- name    : BlindProphetSec.Blind.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:44.318894+00:00
-- url     : https://prove2.me/theorems/66770507-7b92-471c-8139-b7ffd5fb49bf
-- title:
--   Lemma 3.1, p. 7 — P(V_{σ_T} > t) = P(T ≤ j − 1) + Σᵢ P(Vᵢ > t) Σ_{k>j−1} P(T ≥ k | σ_k = i)/n for t ∈ [τⱼ, τⱼ₋₁)
-- statement:
--   Let $V_1,\dots,V_n$ be independent nonnegative random variables, let $\sigma$ be a uniformly random arrival order independent of them, and let $\tau_1\ge\tau_2\ge\dots\ge\tau_n$ be nonincreasing thresholds, with the conventions $\tau_0=+\infty$ and $\tau_{n+1}=-\infty$. Let $T$ be the stopping time of $\mathrm{TTA}_{\tau_1,\dots,\tau_n}$ and $V_{\sigma_T}=V_{\sigma_T}\mathbf 1_{T<\infty}$ the gambler's reward. Then for every $j\in[n+1]$ and every $t\ge0$ with $t\in[\tau_j,\tau_{j-1})$,
--   $$\mathbb P(V_{\sigma_T}>t)=\mathbb P(T\le j-1)+\sum_{i\in[n]}\mathbb P(V_i>t)\left(\sum_{k>j-1}^{n}\frac{\mathbb P(T\ge k\mid\sigma_k=i)}{n}\right).$$
--
--   The identity splits the event that the gambler earns more than $t$ into stopping before time $j$, which happens only above $t$, and stopping later on a value above $t$.
--
--   **Formalization Note.** $\mathbb P(T\ge k\mid\sigma_k=i)$ is written $n\,\mathbb P(T\ge k,\ \sigma_k=i)$, since $\mathbb P(\sigma_k=i)=1/n$; the printed division by $n$ is kept. The hypothesis $t\ge0$ is not printed: for $t<0$ the left side is $1$ (the reward is $0$ when the gambler never stops) while the right side for $j=n+1$ is $\mathbb P(T\le n)$, so the printed statement is false there; the paper only uses $t\ge0$. Continuity of the laws is not assumed (the identity does not use it).
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 7, Lemma 3.1; proof pp. 7–8

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem lemma_3_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hnn : ∀ i, μ i (Set.Iio 0) = 0) (τ : Fin n → ℝ) (hτ : Antitone τ)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n + 1) (t : ℝ) (ht0 : 0 ≤ t)
    (ht_lo : ∀ h : j ≤ n, τ ⟨j - 1, by omega⟩ ≤ t)
    (ht_hi : ∀ h : 2 ≤ j, t < τ ⟨j - 2, by omega⟩) :
    probVS μ (fun v σ => t < ttaReward τ v σ) =
      probVS μ (fun v σ => stopLE (ttaAcc τ v σ) (j - 1)) +
        ∑ i : Fin n, (μ i (Set.Ioi t)).toReal *
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j ≤ k.val + 1),
            ((n : ℝ) * probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i)) / n := by sorry

end BlindProphetSec.Blind
