-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_proposition_3_7_weak
-- name    : ClosedLoopMFG.Limit.proposition_3_7_weak
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:39.685975+00:00
-- url     : https://prove2.me/theorems/009772b7-398f-407c-9902-ca963ae7de25
-- title:
--   Proposition 3.7 (weak MFE part) — under convexity, weak RMFE and weak MFE induce the same measure flows
-- statement:
--   Assume Assumptions A and B. Fix a filtered probability space $(\Omega,\mathcal F,\mathbb F,\mathbb P)$, a process $W$, a process $X^*$ and a flow $\mu$ on it. Then:
--
--   1. if $(\Omega,\mathcal F,\mathbb F,\mathbb P,W,\Lambda^*,X^*,\mu)$ is a weak RMFE for some $\mathcal P(A)$-valued semi-Markov $\Lambda^*$, then $(\Omega,\mathcal F,\mathbb F,\mathbb P,W,\alpha^*,X^*,\mu)$ is a weak MFE for some $A$-valued semi-Markov $\alpha^*$;
--   2. if $(\Omega,\mathcal F,\mathbb F,\mathbb P,W,\alpha^*,X^*,\mu)$ is a weak MFE, then $(\Omega,\mathcal F,\mathbb F,\mathbb P,W,\Lambda^*,X^*,\mu)$ is a weak RMFE for some $\mathcal P(A)$-valued semi-Markov $\Lambda^*$.
--
--   In particular every weak RMFE flow $\mu$ is a weak MFE flow and conversely ("on the level of the measure flow $\mu$").
--
--   **Formalization Note** The paper's Proposition 3.7 also states that every strong RMFE is a strong MFE and conversely; that part is posed in the companion mission on the converse limit theorem (mission 2 of this series). The paper's "every weak MFE is a RMFE" (and its typo "RFME" in the strong half) refer to weak RMFE. Both directions are stated on the same space with the same $W$, $X^*$ and $\mu$, as in the proof in §4.5 (pp. 22–23), which is stronger than equality of the laws of the flows.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 17, Proposition 3.7 (weak part; proof §4.5, pp. 22–23)

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Proposition 3.7, weak part** (p. 17; proof §4.5, pp. 22–23). Under Assumptions A and B, on
the level of the measure flow: on a fixed filtered probability space with fixed `W`, `X*`, `μ`,
if `Λ*` makes the tuple a weak RMFE then some `α*` makes it a weak MFE, and conversely. -/
theorem proposition_3_7_weak {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → E d) (X : Ω → Path d T) (μ : Ω → Flow d T) :
    (∀ Λ : ℝ → E d → Flow d T → PA A, IsWeakRMFE A lam b f g P 𝓕 W Λ X μ →
      ∃ α : ℝ → E d → Flow d T → EA, IsWeakMFE A lam b f g P 𝓕 W α X μ) ∧
    (∀ α : ℝ → E d → Flow d T → EA, IsWeakMFE A lam b f g P 𝓕 W α X μ →
      ∃ Λ : ℝ → E d → Flow d T → PA A, IsWeakRMFE A lam b f g P 𝓕 W Λ X μ) := by sorry

end ClosedLoopMFG.Limit
