-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_eq_19
-- name    : FirstPriceLearning.Adversarial.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:54.052928+00:00
-- url     : https://prove2.me/theorems/fc6b76f2-9a30-4f87-b0ee-3fd327dbaf9c
-- title:
--   Display (19) — grid regret $\le T_0+8\sum_\ell 2^{-\ell}|\Phi^\ell(T)\cap(T_0,T]|$ on the good event
-- statement:
--   Consider a run of ML-IS-UCB with $\gamma\ge3$ and any selection rule against a value sequence $v\in[0,1]^T$ and HOBs $m$ on which the inequalities $|\hat r^\ell_{i,t}-r_{i,t}|\le w^\ell_{i,t}$ of Lemma 7 hold for all $i\in[K]$, $\ell\in[L]$ and $T_0<t\le T$. Then the regret against the best grid bid satisfies
--   $$
--   \sum_{t=1}^T\Big(\max_{i\in[K]}r_{i,t}-r_{i(t),t}\Big)\le T_0+8\sum_{\ell=1}^L2^{-\ell}\cdot\big|\Phi^\ell(T)\cap\{t:T_0<t\le T\}\big|,
--   $$
--   where $i(t)$ is the index of the bid at time $t$ and $\Phi^\ell(T)$ is the set of times assigned to level $\ell$.
--
--   This is the double-counting step: it reduces the regret bound to bounding the number of exploration rounds at each level.
--
--   **Formalization Note** Stated pathwise under the conclusion (17) of Lemma 7, which is how the paper uses it ("provided that the high probability event in Lemma 7 holds").
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 31-32, eq. (19)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Display (19), pp. 31–32: on a run of ML-IS-UCB on which the inequalities (17) of Lemma 7 hold
for all `i ∈ [K]`, `ℓ ∈ [L]`, `T₀ < t ≤ T`, the regret against the best grid bid satisfies
`Σ_{t=1}^T (max_{i ∈ [K]} r_{i,t} - r_{i(t),t}) ≤ T₀ + 8 Σ_{ℓ=1}^L 2^{-ℓ} |Φ^ℓ(T) ∩ {t : T₀ < t ≤ T}|`. -/
theorem eq_19 (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h17 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t) :
    ∑ t ∈ Finset.Icc 1 T, (gridOracle μG v t - gridReward μG v (runIndex T γ sel v m t) t)
      ≤ (initLength T : ℝ) + 8 * ∑ ℓ ∈ Finset.Icc 1 (numLevels T),
          (1 / 2 : ℝ) ^ ℓ *
            (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ) := by sorry

end FirstPriceLearning.Adversarial
