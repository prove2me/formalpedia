-- Prove2me | Theorems.Thm_DRBatchBandit_lemma_5
-- name    : DRBatchBandit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:51.034115+00:00
-- url     : https://prove2.me/theorems/8d40d077-26a1-49dc-9e61-3057dc3c86b1
-- title:
--   Lemma 5, p.17 — the KL dual value is 1-Lipschitz in the sup distance of quantile functions
-- statement:
--   Let $\mathbf P_1,\mathbf P_2$ be probability measures on $\mathbb R$ and $\delta>0$. Then
--   $$\Big|\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P_1}[e^{-Y/\alpha}]-\alpha\delta\}-\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P_2}[e^{-Y/\alpha}]-\alpha\delta\}\Big|\le\sup_{t\in[0,1]}|q_{\mathbf P_1}(t)-q_{\mathbf P_2}(t)|,$$
--   where $q_{\mathbf P}(t)=\inf\{x\in\mathbb R:t\le F_{\mathbf P}(x)\}$ is the $t$-quantile.
--
--   In the proof of Theorem 2 it reduces the error of the robust value estimate to a distance between the empirical and the true reward distributions.
--
--   **Formalization Note** The dual values are extended reals (a non-integrable $e^{-Y/\alpha}$ gives the objective $-\infty$). The absolute difference is stated as two one-sided inequalities $V_1\le V_2+T$ and $V_2\le V_1+T$, for every real $T$ with $|q_{\mathbf P_1}(t)-q_{\mathbf P_2}(t)|\le T$ for all $t\in(0,1)$.
--
--   Differences from the source:
--   - encoding: supremum over α ≥ 0 with the α = 0 value defined by Remark 2 as ess inf → supremum over α > 0; reason: Remark 2 (p.11) defines the α = 0 value as the right limit, so the supremum is unchanged
--   - reading: sup over t ∈ [0, 1] → sup over t ∈ (0, 1); reason: q_P(0) = −∞ for every P, so the printed supremum is undefined at t = 0; q_P(1) can be +∞; the proof uses q_P(U) with U uniform on (0, 1)
--   - encoding: |V₁ − V₂| ≤ sup_t |q₁(t) − q₂(t)| with real dual values → V₁ ≤ V₂ + T ∧ V₂ ≤ V₁ + T in EReal, for every real T bounding |q₁ − q₂| on (0, 1); reason: the dual values can be ±∞ for laws on ℝ; the two inequalities are the absolute-value bound when they are finite and avoid ⊤ − ⊤
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Lemma 5, p.17. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_DRBatchBandit_ScalarDual

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

/-- Lemma 5 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.17): for any probability
measures `P₁, P₂` supported on `ℝ`,
`|sup_{α ≥ 0} {−α log E_{P₁}[exp(−Y/α)] − αδ} − sup_{α ≥ 0} {−α log E_{P₂}[exp(−Y/α)] − αδ}|
  ≤ sup_{t ∈ [0,1]} |q_{P₁}(t) − q_{P₂}(t)|`.

**Formalization Note.** The dual values are in `EReal` (`dualValue`, supremum over `α > 0`); the
absolute difference is stated as the two one-sided inequalities, for every real `T` bounding
`|q_{P₁}(t) − q_{P₂}(t)|` on `t ∈ (0, 1)`. The endpoints are excluded: `q_P(0) = −∞` for every
`P`, and `q_P(1)` may be `+∞`. -/
theorem lemma_5 (P₁ P₂ : Measure ℝ) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |quantile P₁ t - quantile P₂ t| ≤ T) :
    dualValue P₁ δ ≤ dualValue P₂ δ + (T : EReal) ∧
      dualValue P₂ δ ≤ dualValue P₁ δ + (T : EReal) := by sorry

end DRBatchBandit
