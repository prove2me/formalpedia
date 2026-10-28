-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7_heldout
-- name    : FirstPriceLearning.Adversarial.lemma_7_heldout
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T06:45:45.613554+00:00
-- url     : https://prove2.me/theorems/2b59a664-f151-4e35-848c-e54c7887453f
-- title:
--   Lemma 7, displays (p_0_lower), (p_0_upper) — the held-out estimates $\hat p^0_j$ are within a factor 2 of $p_j$ w.p. $\ge1-2(KT)^{-3}$
-- statement:
--   Run ML-IS-UCB (Algorithm 4) with $\gamma\ge3$ and any selection rule against a fixed value sequence $v\in[0,1]^T$, with iid highest other bids $m_t\sim G$, $G$ supported on $[0,1]$. Let $K=\lceil\sqrt T\rceil$ and let $\hat p^0_j=K^{-1}\sum_{t\in\Phi^0(T_0)}\mathbb 1(b^j<m_t\le b^{j+1})$ be the held-out estimate of $p_j=G(b^{j+1})-G(b^j)$ built from the $K$ level-0 initialization rounds $t=1,\dots,K$ (where the bid is $0$). Then for each grid index $j\in[K]$, except on an event of probability at most $2(KT)^{-3}$,
--   $$
--   p_j\le2\Big(\hat p^0_j+\frac{\gamma\log(KT)}{K}\Big)\qquad\text{and}\qquad\hat p^0_j\le2\Big(p_j+\frac{\gamma\log(KT)}{K}\Big).
--   $$
--
--   These are displays (p_0_lower) and (p_0_upper) in the proof of Lemma 7; since $K\hat p^0_j\sim\mathsf B(K,p_j)$ they follow from the Chernoff bounds for the binomial distribution (Lemma (binomial tail) of the Appendix), distinguishing the cases $p_j\le\gamma\log(KT)/K$ and $p_j>\gamma\log(KT)/K$.
--
--   **Formalization note.** The probability is the outer measure, under the product law of $(m_1,\dots,m_T)$, of the failure event. The estimate is the one computed by the formal run from the censored feedback $\max\{b_t,m_t\}$ (`phat0` of `runRecord`/`runFeedback`). The paper states the per-$j$ failure probability $(KT)^{-2}$ loosely; the bound $2(KT)^{-3}$ is what its argument gives with $\gamma\ge3$ and is what the union bound in Lemma 7 needs.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, Appendix C (Proof of Main Lemmas), subsection 'Proof of Lemma 7', displays (p_0_lower) and (p_0_upper)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Displays (p⁰-lower) and (p⁰-upper) in the proof of Lemma 7 (Appendix): for each grid
index `j`, the held-out estimate `p̂⁰_j` built from the `m = ⌈√T⌉` level-0 initialization rounds
satisfies `p_j ≤ 2 (p̂⁰_j + γ log(KT)/m)` and `p̂⁰_j ≤ 2 (p_j + γ log(KT)/m)` except on an event
of probability at most `2 (KT)⁻³`. Stated as an upper bound on the (outer) measure of the
failure event. -/
theorem lemma_7_heldout (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (j : ℕ) (hj : j < numGrid T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ (intervalProb T μG j ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (intervalProb T μG j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)))}
      ≤ ENNReal.ofReal (2 / ((numGrid T : ℝ) * (T : ℝ)) ^ 3) := by sorry

end FirstPriceLearning.Adversarial
