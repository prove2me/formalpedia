-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7
-- name    : FirstPriceLearning.Adversarial.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:00.988185+00:00
-- url     : https://prove2.me/theorems/45ffcfa8-a712-45d2-b51d-27eb6e9df543
-- title:
--   Lemma 7 — the widths $w^\ell_{i,t}$ are valid certificates with probability $\ge 1-4T^{-3}$
-- statement:
--   Run ML-IS-UCB with tuning parameter $\gamma\ge3$ and any selection rule against a fixed value sequence $v\in[0,1]^T$, with iid HOBs $m_t$ drawn from a law $G$ on $[0,1]$. Let $r_{i,t}=R(v_t,b^i)$, let $\hat r^\ell_{i,t}$ be the level-$\ell$ estimate (15), $w^\ell_{i,t}$ the width (13), and $p_j=G(b^{j+1})-G(b^j)$. Then with probability at least $1-4T^{-3}$ the inequalities
--   $$
--   \big|\hat r^\ell_{i,t}-r_{i,t}\big|\le w^\ell_{i,t}\le\gamma\Big(\sqrt{6\log(LKT)\sum_{j\ge i}\tfrac1{n^\ell_{j,t}}\big(p_j+\tfrac{\gamma\log(LKT)}{\lceil\sqrt T\rceil}\big)}+\tfrac{\log(LKT)}{n^\ell_{i,t}}\Big)
--   $$
--   hold simultaneously for all $i\in[K]$, $\ell\in[L]$ and $T_0<t\le T$.
--
--   This is the concentration step of the analysis: the widths, computed before the level-$\ell$ HOBs are used, certify the accuracy of the level-$\ell$ reward estimates, and (18) bounds them by the true interval probabilities.
--
--   **Formalization Note** The statement bounds the outer measure of the failure event under the product law of $(m_1,\dots,m_T)$ by $4/T^3$, so no measurability of the event is required. The quantities are those of the run of the algorithm as functions of $m$, defined for every $(i,\ell,t)$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 31, Lemma 7, eqs. (17), (18)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Lemma 7, p. 31: for `γ ≥ 3`, with probability at least `1 - 4T⁻³` (over the iid HOBs), the
inequalities (17) and (18) hold simultaneously for all grid indices `i`, levels `ℓ ∈ [L]` and
paper times `T₀ < t ≤ T` of the ML-IS-UCB run. Stated as an upper bound on the (outer) measure of
the failure event. -/
theorem lemma_7 (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t}
      ≤ ENNReal.ofReal (4 / (T : ℝ) ^ 3) := by sorry

end FirstPriceLearning.Adversarial
