-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_decomposition_5
-- name    : CappeKLUCB.ExpFam.decomposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:20:07.160996+00:00
-- url     : https://prove2.me/theorems/09a4d349-07b3-490a-bba0-b70c3ee4c6f7
-- title:
--   (5), p. 9 — if arm a is played at round t+1, either μ† ≥ U_{a⋆}(t) or μ† < Uₐ(t)
-- statement:
--   Consider a run of the kl-UCB algorithm (Algorithm 2) with $K$ arms and exploration function $f_1$, and write $U_b(t)$ for the kl-UCB index of arm $b$ after round $t$ and $A_{t+1}$ for the arm pulled at round $t+1$. Let $a$ and $a^\star$ be arms and $\mu^\dagger\in\mathbb R$. For every outcome and every round $t\ge K$, if $A_{t+1} = a$ then
--   $$\{A_{t+1}=a\} \subseteq \{\mu^\dagger \ge U_{a^\star}(t)\}\cup\{\mu^\dagger < U_{a^\star}(t)\text{ and } A_{t+1}=a\} \subseteq \{\mu^\dagger \ge U_{a^\star}(t)\}\cup\{\mu^\dagger < U_a(t)\text{ and } A_{t+1}=a\},$$
--   i.e. both disjunctions hold at that outcome.
--
--   The second inclusion is where the index rule enters: an arm pulled at round $t+1$ has the largest index. This decomposition is the first step of the general regret analysis of §3.1; in the paper $a^\star$ is an optimal arm and $\mu^\dagger$ is $\mu^\star$ or slightly smaller.
--
--   **Formalization Note** The statement is pathwise and uses only the run predicate; it is stated for arbitrary $a$, $a^\star$ and $\mu^\dagger$, as the inclusions hold for all of them.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 9, (5)

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- (5), Cappé et al., arXiv:1210.1136v4, p. 9. -/
theorem decomposition_5 {K : ℕ} (F : ExpFamily) {Ω : Type*}
    (X : Fin K → ℕ → Ω → ℝ) (I : ℕ → Ω → Fin K) (hrun : IsKLUCBRun F f₁ X I)
    (a astar : Fin K) (μdag : ℝ) (t : ℕ) (ht : K ≤ t) (ω : Ω) (hplay : I (t + 1) ω = a) :
    (klucbIndex F f₁ X I astar t ω ≤ μdag ∨
        (μdag < klucbIndex F f₁ X I astar t ω ∧ I (t + 1) ω = a)) ∧
      (klucbIndex F f₁ X I astar t ω ≤ μdag ∨
        (μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a)) := by sorry

end CappeKLUCB.ExpFam
