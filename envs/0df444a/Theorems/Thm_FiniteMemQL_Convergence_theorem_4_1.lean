-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_theorem_4_1
-- name    : FiniteMemQL.Convergence.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:17.532332+00:00
-- url     : https://prove2.me/theorems/77c15522-34ea-4f7a-8366-20f68d9acf3e
-- title:
--   Theorem 4.1, p. 15 — finite-window Q-learning converges a.s. to Q* of (4.5), and its greedy policy loses at most 2‖c‖∞/(1−β) Σ βᵗ L_t
-- statement:
--   Assume Assumption 4.1: actions are explored i.i.d. with a law $\sigma$ charging every action; the hidden state is positive Harris recurrent under this exploration, with invariant probability measure $\pi^*$; the step sizes are $\alpha_t(I,u)=1/(1+\sum_{k\le t}\mathbb 1\{(I_k,U_k)=(I,u)\})$ at visits and $0$ otherwise; and every pair $(I,u)$ is visited infinitely often. Then
--
--   1. the finite-window Q-learning iterates (4.1) converge almost surely to the solution $Q^*$ of (4.5);
--   2. for every policy $\gamma^N$ with $Q^*(I,\gamma^N(I))=\min_uQ^*(I,u)$, used from time $N$ on after a policy has acted on the first $N$ steps, with $\pi_0^-$ the prior of $X_0$,
--   $$
--   E\bigl[J_\beta(\hat z_0,\gamma^N)-J^*_\beta(\hat z_0)\bigr]\le\frac{2\|c\|_\infty}{1-\beta}\sum_{t=0}^\infty\beta^tL_t,
--   $$
--   where $\hat z_0=(\pi_0^-,I_0^N)$ and $L_t$ is the filter-stability term (3.9) for $\pi^*$.
--
--   Finite-memory Q-learning thus converges without a belief computation, and the policy it learns is near optimal whenever the filter is stable.
--
--   **Formalization Note** Assumption 4.1.2 is assumed for the i.i.d. exploration actually run, not for every stationary exploration policy; uniqueness of $\pi^*$ follows from positive Harris recurrence. The iteration starts at time $N$, when the first window exists. In (ii) the conditioning on $I_0^N$ is read as the expectation over $I_0^N$, as in Theorems 3.2 and 3.3, and the policy on the first $N$ steps is an arbitrary deterministic observation-history policy.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 15, §4, Theorem 4.1 with Assumption 4.1 (proof pp. 16–18, Appendix A)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Definitions.Def_FiniteMemQL_Convergence_Learning

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Theorem 4.1, p. 15 (arXiv:2103.12158v4). Under Assumption 4.1 (step sizes as in `qIter`;
positive Harris recurrence of the state under the i.i.d. exploration `σ`, with invariant law `π*`;
every `(I, u)` visited infinitely often):
(i) the finite-window Q-learning iterates (4.1) converge almost surely to `Q*` of (4.5);
(ii) for every policy `γ^N` greedy for `Q*`, started at time `N` after a history policy `γ₀` has
acted on the first `N` steps, in expectation over the first window `I₀ᴺ`,
`E[ J_β((π₀, I₀ᴺ), γ^N) − J*_β(π₀, I₀ᴺ) ] ≤ 2‖c‖∞ / (1 − β) Σ_t β^t L_t`. -/
theorem theorem_4_1 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ] (hσ : ∀ u : U, 0 < σ {u})
    (hHarris : RiskSensMDP.AverageCost.IsPositiveHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs) :
    (∀ (μ : Measure X), IsProbabilityMeasure μ → ∀ Q₀ : Window Y U N → U → ℝ,
      (∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
        ∃ᶠ t in atTop, winAt (N := N) ω t = I ∧ (ω t).2.2 = u) →
      ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
        Tendsto (fun n : ℕ => qIter M Q₀ ω n I u) atTop (𝓝 (qStar M πs I u))) ∧
    (∀ (π₀ : Measure X), IsProbabilityMeasure π₀ → ∀ (γ₀ : HistPolicy Y U)
      (γN : Window Y U N → U), (∀ I : Window Y U N, qStar M πs I (γN I) = ⨅ u : U, qStar M πs I u) →
      ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
          (Jpol M γN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
            JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)) ≤
        2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t) := by sorry

end FiniteMemQL.Convergence
