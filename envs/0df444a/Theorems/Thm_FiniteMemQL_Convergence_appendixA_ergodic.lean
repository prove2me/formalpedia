-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_appendixA_ergodic
-- name    : FiniteMemQL.Convergence.appendixA_ergodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:17.484181+00:00
-- url     : https://prove2.me/theorems/13d9e812-291b-40bc-b4e6-6536987f1031
-- title:
--   Appendix A, p. 28 — ergodic averages along the extended window process converge to their stationary expectation under P^{π*}
-- statement:
--   Assume actions are explored i.i.d. with a law $\sigma$ charging every action, that the hidden state chain $P_\sigma$ is positive Harris recurrent, and that $\pi^*$ is its invariant probability measure. Let the process start from any initial law $\mu$. Then for every measurable function $f$ of the extended window $(X_k,Y_{[k-N,k+1]},U_{[k-N,k]})$ that is integrable with respect to $P^{\pi^*}$, almost surely
--   $$
--   \lim_{t\to\infty}\frac1t\sum_{k=N}^{N+t-1}f\bigl(X_k,Y_{[k-N,k+1]},U_{[k-N,k]}\bigr)=\int f\,dP^{\pi^*},
--   $$
--   where $P^{\pi^*}$ is the law of the extended window when $X_0\sim\pi^*$ (the process is then stationary). This is the averaging step behind the convergence of the Q-learning iterates.
--
--   **Formalization Note** The paper states it for "any measurable $f$"; the right-hand side exists only for $f$ integrable under $P^{\pi^*}$, so integrability is assumed (the ergodic theorem for positive Harris chains holds for every such $f$ and every initial law). The paper writes the extended window with $X_{k-1}$ in one display and $X_k$ in the next; the statement uses $X_k$, the state at which the cost $c(X_k,U_k)$ is incurred.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 28, Appendix A

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Definitions.Def_FiniteMemQL_Convergence_Learning

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Appendix A, p. 28 (arXiv:2103.12158v4): ergodic averages of the extended window process.
Under the i.i.d. exploration `σ` with positive Harris recurrent state process and invariant law
`π*`, for every initial law `μ` and every measurable `f` of the extended window
`(X_k, Y_{[k−N,k+1]}, U_{[k−N,k]})` that is integrable under `P^{π*}`, almost surely
`(1/n) Σ_{k<n} f(extended window at N + k) → ∫ f dP^{π*}`, where `P^{π*}` is the law of the extended
window when `X_0 ~ π*` (a stationary process). The page's "any measurable f" needs
integrability for the right-hand side to exist; integrability under `P^{π*}` is that condition. -/
theorem appendixA_ergodic {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ] (hσ : ∀ u : U, 0 < σ {u})
    (hHarris : RiskSensMDP.AverageCost.IsPositiveHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × Window Y U (N + 1) → ℝ) (hf : Measurable f)
    (hfi : Integrable f ((pathMeasure M πs σ).map (fun ω => extWin (N := N) ω N))) :
    ∀ᵐ ω ∂pathMeasure M μ σ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (extWin (N := N) ω (N + k))) atTop
      (𝓝 (∫ p, f p ∂((pathMeasure M πs σ).map (fun ω => extWin (N := N) ω N)))) := by sorry

end FiniteMemQL.Convergence
