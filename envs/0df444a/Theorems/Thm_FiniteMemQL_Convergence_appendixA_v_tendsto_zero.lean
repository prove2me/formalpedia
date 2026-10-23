-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_appendixA_v_tendsto_zero
-- name    : FiniteMemQL.Convergence.appendixA_v_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:08.14848+00:00
-- url     : https://prove2.me/theorems/40baa098-39b6-44a8-b891-893e943b4695
-- title:
--   Appendix A, p. 28 — the auxiliary iterates v_t(I, u) tend to 0 almost surely for every (I, u)
-- statement:
--   Under the hypotheses of Theorem 4.1 — i.i.d. exploration with a law $\sigma$ charging every action, positive Harris recurrence of the hidden state under it with invariant probability measure $\pi^*$, and every pair $(I,u)$ visited infinitely often almost surely — the iterates
--   $$
--   v_{t+1}(I,u)=(1-\alpha_t(I,u))\,v_t(I,u)+\alpha_t(I,u)\,r^*_t(I,u),\qquad v_N=0,
--   $$
--   with the step sizes of Assumption 4.1.1 and $r^*_t$ as on p. 16, satisfy $v_t(I,u)\to0$ almost surely for all $(I,u)$. This is the part of the decomposition $\Delta_t=\delta_t+u_t+v_t$ of the Q-learning error that carries the non-Markovian window transitions.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 28, Appendix A (and p. 16)

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Definitions.Def_FiniteMemQL_Convergence_Learning

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Appendix A, p. 28 (arXiv:2103.12158v4): `v_t(I, u) → 0` almost surely for all `(I, u)`, where
`v_{t+1} = (1 − α_t) v_t + α_t r*_t` with the step sizes of Assumption 4.1.1 (p. 16). Hypotheses:
i.i.d. exploration `σ` with full support, positive Harris recurrence of the state under it,
`π*` invariant, and Assumption 4.1.3 (every `(I, u)` visited infinitely often a.s.). -/
theorem appendixA_v_tendsto_zero {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ] (hσ : ∀ u : U, 0 < σ {u})
    (hHarris : RiskSensMDP.AverageCost.IsPositiveHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hvisit : ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      ∃ᶠ t in atTop, winAt (N := N) ω t = I ∧ (ω t).2.2 = u) :
    ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
      Tendsto (fun n : ℕ => vIter M πs ω n I u) atTop (𝓝 0) := by sorry

end FiniteMemQL.Convergence
