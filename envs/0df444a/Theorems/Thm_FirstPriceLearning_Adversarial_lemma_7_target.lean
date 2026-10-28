-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7_target
-- name    : FirstPriceLearning.Adversarial.lemma_7_target
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T06:45:18.738206+00:00
-- url     : https://prove2.me/theorems/1553b714-33d6-4af6-822f-b8ae072c235a
-- title:
--   Lemma 7, display (target) — $\mathbb P(|\hat r^\ell_{i,t}-r_{i,t}|\ge\gamma(\sqrt{\log(LKT)\sum_{j\ge i}p_j/n^\ell_{j,t}}+\log(LKT)/n^\ell_{i,t}))\le2(LKT)^{-4}$
-- statement:
--   Run ML-IS-UCB (Algorithm 4) with tuning parameter $\gamma\ge3$ and any selection rule against a fixed value sequence $v\in[0,1]^T$, with iid highest other bids $m_1,\dots,m_T\sim G$, $G$ supported on $[0,1]$. Write $L=\lceil\log_2T\rceil$, $K=\lceil\sqrt T\rceil$, $T_0=(L+1)K$, $r_{i,t}=R(v_t,b^i)=(v_t-b^i)G(b^i)$, $p_j=G(b^{j+1})-G(b^j)$, and let $\hat r^\ell_{i,t}$ be the level-$\ell$ reward estimate (15) and $n^\ell_{j,t}$ the level-$\ell$ observation counts (12) of the run. Then for every fixed grid index $i\in[K]$, level $\ell\in[L]$ and time $T_0<t\le T$,
--   $$
--   \mathbb P\Big(\big|\hat r^\ell_{i,t}-r_{i,t}\big|\ge\gamma\Big(\sqrt{\log(LKT)\textstyle\sum_{j\ge i}p_j/n^\ell_{j,t}}+\log(LKT)/n^\ell_{i,t}\Big)\Big)\le\frac{2}{(LKT)^4}.
--   $$
--
--   This is display (target) in the proof of Lemma 7. In the paper it follows from the Bernstein inequality applied, conditionally on the level-$\ell$ bids, to $\sum_{s\in\Phi^\ell(t-1)}X_s$ with $X_s=\sum_{j\ge i}\mathbb 1(b_s\le b^j)(\mathbb 1(b^j<m_s\le b^{j+1})-p_j)/n^\ell_{j,t}$: by Lemma 6 the level-$\ell$ HOBs are independent of the level-$\ell$ bids, each $X_s$ is centred with range at most $1/n^\ell_{i,t}$, and the total variance is at most $\sum_{j\ge i}p_j/n^\ell_{j,t}$.
--
--   **Formalization note.** The probability is the outer measure, under the product law of $(m_1,\dots,m_T)$, of the deviation event, so no measurability is required in the statement. All quantities are those of the formal run of the algorithm (`runRhat`, `runN`, `gridReward`, `intervalProb`).
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, Appendix C (Proof of Main Lemmas), subsection 'Proof of Lemma 7', display (target)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Display (target) in the proof of Lemma 7 (Appendix): for each grid index `i`, level
`ℓ ∈ [L]` and paper time `T₀ < t ≤ T`, with probability at least `1 - 2 (LKT)⁻⁴` over the iid
HOBs, `|r̂^ℓ_{i,t} - r_{i,t}| < γ (√(log(LKT) Σ_{j ≥ i} p_j / n^ℓ_{j,t}) + log(LKT) / n^ℓ_{i,t})`.
Stated as an upper bound on the (outer) measure of the deviation event. -/
theorem lemma_7_target (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (i : ℕ) (hi : i < numGrid T) (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (numLevels T))
    (t : ℕ) (ht₀ : initLength T < t) (htT : t ≤ T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | γ * (Real.sqrt (logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + logFactor T / (runN T γ sel v m ℓ i t : ℝ))
            ≤ |runRhat T γ sel v m ℓ i t - gridReward μG v i t|}
      ≤ ENNReal.ofReal (2 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4) := by sorry

end FirstPriceLearning.Adversarial
