-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_16
-- name    : FirstPriceLearning.Adversarial.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:19.002103+00:00
-- url     : https://prove2.me/theorems/01e74445-9866-4ebc-a22a-c7d119b3a776
-- title:
--   Lemma 16 — $\sum_t\sum_{j\ge i(t)}v_j/n_{j,t}\le s(1+\log T)$ and $\sum_t 1/n_{i(t),t}\le K(1+\log T)$
-- statement:
--   Let $\Phi\subseteq[T]$ be a set of times, let $i(t)$ be grid indices with bids $b_t=b^{i(t)}$ on a grid of $K$ points, and let
--   $$
--   n_{j,t}=\sum_{s\in\Phi,\,s<t}\mathbb 1(b_s\le b^j)
--   $$
--   as in (12). Assume that $\Phi$ contains at least $\lceil\sqrt T\rceil$ times $s\le T_0$ at which the bid is $b^1=0$. Then for every vector $(w_1,\dots,w_K)$ with nonnegative entries and $\sum_{j=1}^Kw_j=s$,
--   $$
--   \sum_{t>T_0:\,t\in\Phi}\ \sum_{j\ge i(t)}\frac{w_j}{n_{j,t}}\le s(1+\log T),\qquad
--   \sum_{t>T_0:\,t\in\Phi}\frac1{n_{i(t),t}}\le K(1+\log T).
--   $$
--
--   This deterministic counting lemma, valid for any level decomposition and any bidding sequence, is the key combinatorial input to Lemma 9.
--
--   **Formalization Note** The paper names the vector $(v_1,\dots,v_K)$; it is renamed $w$ here because $v$ is the value sequence. The initialization hypothesis is added (slip 10): the printed statement says "any subset $\Phi^\ell(T)\subseteq[T]$", but the proof (p. 44) uses $n^\ell_{j,t}=\lceil\sqrt T\rceil+\sum_{s\in\Phi^\ell(T),T_0<s<t}\mathbb 1(b_s\le b^j)$, which holds because each level contains its initialization block of $\lceil\sqrt T\rceil$ zero bids; without it $n_{j,t}$ may vanish. $K$ and $T_0$ are arbitrary here; the grid indices are 0-based.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 43, Lemma 16 (proof p. 44)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Lemma 16, p. 43 (deterministic): let `Φ ⊆ [T]` be a set of times, `idx` a sequence of grid
indices (the bid at time `s` is `b^{idx s}`), and `n_{j,t} = Σ_{s ∈ Φ, s < t} 𝟙(b_s ≤ b^j)` as in
(12). Assume, as the proof on p. 44 does, that `Φ` contains at least `⌈√T⌉` times `s ≤ T₀` with bid
`b^1 = 0` (the initialization block of the level). Then for every nonnegative vector
`(w_1, …, w_K)` with `Σ_j w_j = s`,
`Σ_{t > T₀, t ∈ Φ} Σ_{j ≥ i(t)} w_j / n_{j,t} ≤ s (1 + log T)` and
`Σ_{t > T₀, t ∈ Φ} 1 / n_{i(t),t} ≤ K (1 + log T)`. -/
theorem lemma_16 (T K T₀ : ℕ) (Φ : Finset ℕ) (hΦ : Φ ⊆ Finset.Icc 1 T) (idx : ℕ → ℕ)
    (hidx : ∀ t ∈ Φ, idx t < K)
    (hinit : numGrid T ≤ (Φ.filter (fun r => r ≤ T₀ ∧ idx r = 0)).card)
    (w : ℕ → ℝ) (hw : ∀ j < K, 0 ≤ w j) (s : ℝ) (hs : ∑ j ∈ Finset.range K, w j = s) :
    (∑ t ∈ Φ.filter (fun t => T₀ < t), ∑ j ∈ Finset.Ico (idx t) K,
        w j / (obsCount K Φ idx j t : ℝ) ≤ s * (1 + Real.log T)) ∧
    (∑ t ∈ Φ.filter (fun t => T₀ < t), 1 / (obsCount K Φ idx (idx t) t : ℝ)
        ≤ (K : ℝ) * (1 + Real.log T)) := by sorry

end FirstPriceLearning.Adversarial
