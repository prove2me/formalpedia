-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_decomposition_5
-- name    : CappeKLUCB.Empirical.decomposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:13.928402+00:00
-- url     : https://prove2.me/theorems/a2bfae36-e031-4203-a1b3-e97f21edab3d
-- title:
--   (5), p. 9 — for Algorithm 3, if arm a is played at round t+1, then μ† ≥ U_{a⋆}(t) or μ† < U_a(t)
-- statement:
--   Consider a run of the empirical KL-UCB algorithm (Algorithm 3) with any exploration function $f$, on any realization of the reward stacks. Let $a$ and $a^\star$ be arms, $\mu^\dagger\in\mathbb R$ and $t\ge K$. If arm $a$ is pulled at round $t+1$, then
--   $$A_{t+1}=a \;\Longrightarrow\; \bigl(\mu^\dagger\ge U_{a^\star}(t)\bigr) \text{ or } \bigl(\mu^\dagger< U_{a^\star}(t) \text{ and } A_{t+1}=a\bigr),$$
--   and also
--   $$A_{t+1}=a \;\Longrightarrow\; \bigl(\mu^\dagger\ge U_{a^\star}(t)\bigr) \text{ or } \bigl(\mu^\dagger< U_{a}(t) \text{ and } A_{t+1}=a\bigr),$$
--   that is, $\{A_{t+1}=a\}\subseteq\{\mu^\dagger\ge U_{a^\star}(t)\}\cup\{\mu^\dagger<U_{a^\star}(t),\ A_{t+1}=a\}\subseteq\{\mu^\dagger\ge U_{a^\star}(t)\}\cup\{\mu^\dagger<U_a(t),\ A_{t+1}=a\}$.
--
--   In the paper $a^\star$ is an optimal arm and $\mu^\dagger$ is $\mu^\star$ or slightly smaller; the decomposition splits the draws of a suboptimal arm into rounds where the optimal arm's index is too low and rounds where the suboptimal arm's index is too high.
--
--   **Formalization Note** The statement is pathwise and holds for every real $\mu^\dagger$, every pair of arms and every exploration function, so no probabilistic hypothesis and no optimality of $a^\star$ is assumed; this is a stronger statement than the page's. Rounds are $t+1$ with $t\ge K$, the rounds at which Algorithm 3 uses its indices.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 9, (5), for Algorithm 3 of p. 15

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- Decomposition (5), Cappé et al., arXiv:1210.1136v4, p. 9, for Algorithm 3 (p. 15): if arm `a` is
played at round `t + 1 > K`, then `μ† ≥ U_{a⋆}(t)` or (`μ† < U_{a⋆}(t)` and `A_{t+1} = a`), and
also `μ† ≥ U_{a⋆}(t)` or (`μ† < U_a(t)` and `A_{t+1} = a`). -/
theorem decomposition_5 {K : ℕ} {Ω : Type*} (X : Fin K → ℕ → Ω → ℝ) (I : ℕ → Ω → Fin K)
    (f : ℕ → ℝ) (hrun : IsEmpKLUCBRun f X I) (a astar : Fin K) (μdag : ℝ) (ω : Ω) (t : ℕ)
    (ht : K ≤ t) (hplay : I (t + 1) ω = a) :
    (μdag ≥ index f X I astar t ω ∨ (μdag < index f X I astar t ω ∧ I (t + 1) ω = a)) ∧
    (μdag ≥ index f X I astar t ω ∨ (μdag < index f X I a t ω ∧ I (t + 1) ω = a)) := by sorry

end CappeKLUCB.Empirical
