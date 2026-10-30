-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_lemma_B_1
-- name    : FiniteMemQL.Convergence.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:58.663993+00:00
-- url     : https://prove2.me/theorems/fe526fac-f8f3-42c6-9ee3-8f2cd1f1c23e
-- title:
--   Lemma B.1, p. 29 — the predictive laws of the next observation are no farther apart in total variation than the window posteriors
-- statement:
--   Let $\pi,\pi^*$ be probability measures on $\mathbb X$, viewed as priors on the state $X_{t-N}$ at the oldest time of a window $I=(y_{t-N},\dots,y_t;u_{t-N},\dots,u_{t-1})$, and let $u_t\in\mathbb U$. Then
--   $$
--   \bigl\|P^{\pi}(Y_{t+1}\in\cdot\mid I,u_t)-P^{\pi^*}(Y_{t+1}\in\cdot\mid I,u_t)\bigr\|_{TV}
--   \le\bigl\|P^{\pi}(X_t\in\cdot\mid I)-P^{\pi^*}(X_t\in\cdot\mid I)\bigr\|_{TV}.
--   $$
--   This data-processing inequality is used in the proof of Theorem 3.2 to compare the transition weights of the true and the approximate finite-window models.
--
--   **Formalization Note** Both sides carry the same factor $2$ of the paper's total variation norm, so the statement uses $\sup_B|\mu(B)-\nu(B)|$ (`MarkovChainCLT.tvDist`). The paper's index set $\mathbb Y^N\times\mathbb U^N$ is read as $\mathbb Y^{N+1}\times\mathbb U^{N+1}$ (window plus current action), as the displayed tuple requires. On a window of probability zero the posterior is the zero measure.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 29, Appendix B, Lemma B.1

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Lemma B.1 (arXiv:2103.12158v4, p. 29). For prior laws `π, π*` of the state at the oldest time
of a window `I` and an action `u`, the total variation distance between the predictive laws of the
next observation is at most that between the window posteriors. Both sides of the printed
inequality carry the paper's factor 2 (`‖·‖_TV = 2 sup_B`), so it is stated with `tvDist`. The
printed index set `Y^N × U^N` is a slip for `Y^(N+1) × U^(N+1)`: the window has `N + 1`
observations and, with `u`, `N + 1` actions. -/
theorem lemma_B_1 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (π πs : Measure X) [IsProbabilityMeasure π] [IsProbabilityMeasure πs]
    (I : Window Y U N) (u : U) :
    MarkovChainCLT.tvDist (predYMeasure M π I u) (predYMeasure M πs I u) ≤
      MarkovChainCLT.tvDist (post M π I) (post M πs I) := by sorry

end FiniteMemQL.Convergence
