-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_8
-- name    : FirstPriceLearning.Adversarial.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:09.956304+00:00
-- url     : https://prove2.me/theorems/cc300d22-a5c0-4496-8967-a935bd8a5ba2
-- title:
--   Lemma 8 — on the good event the optimal grid bid survives and the regret at a level-$\ell$ time is $\le 8\cdot2^{-\ell}$
-- statement:
--   Consider a run of ML-IS-UCB with $\gamma\ge3$ and any selection rule against a value sequence $v\in[0,1]^T$ and HOBs $m$ on which the inequalities $|\hat r^\ell_{i,t}-r_{i,t}|\le w^\ell_{i,t}$ of Lemma 7 hold for all $i\in[K]$, $\ell\in[L]$ and $T_0<t\le T$. Let $T_0<t\le T$ and let $\ell$ be the level of $t$, i.e. $t\in\Phi^\ell(T)$. Then:
--
--   1. every maximiser $i^\star$ of $i\mapsto r_{i,t}$ over $[K]$ belongs to the candidate set $\mathcal B^{\ell'}_t$ for every level $\ell'<\ell$, that is, it is never eliminated at time $t$;
--   2. the instantaneous regret satisfies
--   $$
--   \max_{i\in[K]}r_{i,t}-r_{i(t),t}\le 8\cdot2^{-\ell},
--   $$
--   where $i(t)$ is the index of the bid $b_t=b^{i(t)}$.
--
--   This turns the certificates of Lemma 7 into a per-round regret bound indexed by the level at which the round explores.
--
--   **Formalization Note** The lemma is stated pathwise: the hypothesis is the conclusion (17) of Lemma 7 on the given run. $\gamma\ge3$ guarantees that the inner loop of Algorithm 4 always breaks, so the level of $t$ is a level at which the exploration test succeeded. The candidate sets computed at time $t$ are $\mathcal B^0_t,\dots,\mathcal B^{\ell-1}_t$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 31, Lemma 8

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Lemma 8, p. 31: on a run of ML-IS-UCB on which the inequalities (17) of Lemma 7 hold for all
`i ∈ [K]`, `ℓ ∈ [L]`, `T₀ < t ≤ T`, every paper time `T₀ < t ≤ T` with `t ∈ Φ^ℓ(T)` satisfies:
(a) every maximiser `i⋆` of `i ↦ r_{i,t}` over the grid lies in the candidate set `ℬ^{ℓ'}_t` for
every level `ℓ' < ℓ` that the bidder computes at time `t` (it is never eliminated), and
(b) the instantaneous regret `max_{i ∈ [K]} r_{i,t} - r_{i(t),t}` is at most `8 · 2^{-ℓ}`. -/
theorem lemma_8 (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h17 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t) :
    ∀ t : ℕ, initLength T < t → t ≤ T →
      (∀ istar < numGrid T, (∀ i < numGrid T, gridReward μG v i t ≤ gridReward μG v istar t) →
        ∀ ℓ' < runLevel T γ sel v m t, istar ∈ runCand T γ sel v m ℓ' t) ∧
      gridOracle μG v t - gridReward μG v (runIndex T γ sel v m t) t
        ≤ 8 * (1 / 2 : ℝ) ^ runLevel T γ sel v m t := by sorry

end FirstPriceLearning.Adversarial
