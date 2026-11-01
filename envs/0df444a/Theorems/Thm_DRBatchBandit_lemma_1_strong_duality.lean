-- Prove2me | Theorems.Thm_DRBatchBandit_lemma_1_strong_duality
-- name    : DRBatchBandit.lemma_1_strong_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:58.046847+00:00
-- url     : https://prove2.me/theorems/0d9bd580-dacb-48d0-a833-5f8ac6a1bc21
-- title:
--   Lemma 1 (Strong Duality), p.11 — $Q_{\mathrm{DRO}}(\pi)=\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P_0}[e^{-Y(\pi(X))/\alpha}]-\alpha\delta\}$ and its importance-weighted form
-- statement:
--   Assume unconfoundedness, overlap $\pi_0(a\mid x)\ge\eta>0$ and bounded rewards $0\le Y(a^i)\le M$ (Assumption 1), and let $\delta>0$. For any policy $\pi$,
--   $$\inf_{\mathbf P\in\mathcal U_{\mathbf P_0}(\delta)}\mathbf E_{\mathbf P}[Y(\pi(X))]=\sup_{\alpha\ge0}\big\{-\alpha\log\mathbf E_{\mathbf P_0}[\exp(-Y(\pi(X))/\alpha)]-\alpha\delta\big\}\tag{1}$$
--   $$=\sup_{\alpha\ge0}\Big\{-\alpha\log\mathbf E_{\mathbf P_0*\pi_0}\Big[\frac{\exp(-Y(A)/\alpha)\mathbf 1\{\pi(X)=A\}}{\pi_0(A\mid X)}\Big]-\alpha\delta\Big\}.\tag{2}$$
--
--   The left side is $Q_{\mathrm{DRO}}(\pi)$. The identity replaces an infimum over an infinite-dimensional set of laws by a one-dimensional problem in $\alpha$ whose expectation is under the data-generating law, which is what makes the plug-in estimator $\hat Q_{\mathrm{DRO}}$ possible.
--
--   **Formalization Note** Both equalities are stated, as one conjunction. The suprema are over $\alpha>0$. The policy is measurable.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: supremum over α ≥ 0 with the α = 0 value defined by Remark 2 as ess inf → supremum over α > 0; reason: Remark 2 (p.11) defines the α = 0 value as the right limit, so the supremum is unchanged
--   - reading: a policy π (no measurability stated) → π measurable; reason: the expectations E[Y(π(X))] presuppose a measurable π
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Lemma 1, p.11 (equations (1) and (2)); Remark 2, p.11. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue
import Definitions.Def_DRBatchBandit_Assumptions

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Lemma 1, Strong Duality (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.11): for any
policy `π`,
`inf_{P ∈ 𝒰_{P₀}(δ)} E_P[Y(π(X))] = sup_{α ≥ 0} {−α log E_{P₀}[exp(−Y(π(X))/α)] − αδ}` (1)
`= sup_{α ≥ 0} {−α log E_{P₀∗π₀}[exp(−Y(A)/α) 1{π(X) = A} / π₀(A | X)] − αδ}` (2).

**Formalization Note.** Under Assumption 1 (overlap `Overlap M η`, bounded rewards
`BoundedReward M Mrew`; unconfoundedness is built into `M.law`) and `δ > 0` (Definition 2). The
policy is assumed measurable. The suprema are over `α > 0`: Remark 2 (p.11) defines the `α = 0`
value as the essential infimum of `Y(π(X))`, which is the right limit and does not change the
supremum. -/
theorem lemma_1_strong_duality {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η Mrew δ : ℝ) (hov : Overlap M η) (hbd : BoundedReward M Mrew) (hδ : 0 < δ)
    (π : X → Fin d) (hπ : Measurable π) :
    QDRO M δ π = ⨆ α : Set.Ioi (0 : ℝ),
        (-(α : ℝ) * Real.log (∫ z, Real.exp (-z.2 (π z.1) / α) ∂(P0 M)) - α * δ) ∧
    QDRO M δ π = ⨆ α : Set.Ioi (0 : ℝ),
        (-(α : ℝ) * Real.log (∫ ω, Real.exp (-ω.2.1 ω.2.2 / α) *
            (if π ω.1 = ω.2.2 then 1 else 0) / M.e ω.1 ω.2.2 ∂M.law) - α * δ) := by sorry

end DRBatchBandit
