-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_9
-- name    : FirstPriceLearning.Adversarial.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:04.852077+00:00
-- url     : https://prove2.me/theorems/d28d90de-8a31-49a0-9fb6-da8bac8db0dc
-- title:
--   Lemma 9 — $2^{-\ell}|\Phi^\ell(T)\cap(T_0,T]|\le10\gamma^{3/2}\log(LKT)(1+\log T)\sqrt T$
-- statement:
--   Consider a run of ML-IS-UCB with $\gamma\ge3$ and any selection rule against a value sequence $v\in[0,1]^T$ and HOBs $m$, with HOB law $G$ on $[0,1]$, on which the widths satisfy the bound (18) of Lemma 7,
--   $$
--   w^\ell_{i,t}\le\gamma\Big(\sqrt{6\log(LKT)\sum_{j\ge i}\tfrac1{n^\ell_{j,t}}\big(p_j+\tfrac{\gamma\log(LKT)}{\lceil\sqrt T\rceil}\big)}+\tfrac{\log(LKT)}{n^\ell_{i,t}}\Big),
--   $$
--   for all $i\in[K]$, $\ell\in[L]$ and $T_0<t\le T$. Then for each $\ell\in[L]$,
--   $$
--   2^{-\ell}\cdot\big|\Phi^\ell(T)\cap\{t:T_0<t\le T\}\big|\le10\gamma^{3/2}\log(LKT)(1+\log T)\cdot\sqrt T.
--   $$
--
--   The number of exploration rounds at level $\ell$ is thus $\widetilde O(2^\ell\sqrt T)$, which, combined with (19), gives the $\widetilde O(\sqrt T)$ regret.
--
--   **Formalization Note** The printed lemma has no hypothesis, but step (a) of its proof uses (18) of Lemma 7 (slip 9); it is therefore stated pathwise under that bound. Here $p_j=G(b^{j+1})-G(b^j)$ and $\gamma^{3/2}$ is a real power.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 32, Lemma 9

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Lemma 9, p. 32: on a run of ML-IS-UCB with `γ ≥ 3` on which the bound (18) of Lemma 7 on the
widths holds for all `i ∈ [K]`, `ℓ ∈ [L]`, `T₀ < t ≤ T`, for each level `ℓ ∈ [L]`
`2^{-ℓ} · |Φ^ℓ(T) ∩ {t : T₀ < t ≤ T}| ≤ 10 γ^{3/2} log(LKT) (1 + log T) √T`. -/
theorem lemma_9 (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h18 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t) :
    ∀ ℓ ∈ Finset.Icc 1 (numLevels T),
      (1 / 2 : ℝ) ^ ℓ *
          (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ)
        ≤ 10 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * Real.sqrt T := by sorry

end FirstPriceLearning.Adversarial
