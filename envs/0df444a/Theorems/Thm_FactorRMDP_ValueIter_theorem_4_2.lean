-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_theorem_4_2
-- name    : FactorRMDP.ValueIter.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:29.225018+00:00
-- url     : https://prove2.me/theorems/92b5da23-d751-4a04-8eb5-097c06deb0f9
-- title:
--   Theorem 4.2 (corrected: existence form) — a deterministic robust solution (π*, W*) is a saddle point, and max-min = min-max
-- statement:
--   Consider a robust MDP whose factor matrix uncertainty set is r-rectangular and a discount factor $\lambda\in(0,1)$. Then there is a solution $(\pi^*,W^*)$ of the robust MDP problem, with $\pi^*$ deterministic, such that
--
--   $$W^*\in\arg\min_{W\in\mathcal W} R(\pi^*,W) \qquad\text{and}\qquad \pi^*\in\arg\max_{\pi\in\Pi} R(\pi,W^*), \tag{4.6}$$
--
--   and the strong min-max duality holds, with both sides attained at the common value $R(\pi^*,W^*)$:
--
--   $$\max_{\pi\in\Pi}\min_{W\in\mathcal W} R(\pi,W) = R(\pi^*,W^*) = \min_{W\in\mathcal W}\max_{\pi\in\Pi} R(\pi,W). \tag{4.7}$$
--
--   The robust optimal policy is therefore the optimal nominal policy of the MDP in which the adversary plays $W^*$: the pair is an equilibrium of the zero-sum game between decision maker and adversary.
--
--   The paper states (4.6) for every solution $(\pi^*,W^*)$ with $\pi^*$ deterministic. That reading is false: with two states, two actions and $r=2$ one can build an r-rectangular instance in which every policy is robust-optimal, yet for a robust solution $(\pi^*,W^*)$ another policy does strictly better than $\pi^*$ against $W^*$. We state that some solution with $\pi^*$ deterministic satisfies (4.6), which is what the proof of Theorem 5.1 uses; (4.7) is as printed.
--
--   **Formalization Note** Maxima and minima are greatest and least elements (`IsGreatest`, `IsLeast`), so attainment is part of the claim. $\max_{\pi\in\Pi}R(\pi,W)$ is the definition file's `maxR`. The oracle part of Assumption 2.4 is not formalized.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 8, Theorem 4.2, (4.6), (4.7); proof pp. 8–9

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Theorem 4.2, corrected to its existence form (Goyal and Grand-Clément, arXiv:1811.00215v8,
p. 8). If the uncertainty set is r-rectangular, there is a solution `(π*, W*)` of the robust MDP
problem with `π*` deterministic such that (4.6) holds: `W* ∈ argmin_{W ∈ 𝒲} R(π*, W)` and
`π* ∈ argmax_{π ∈ Π} R(π, W*)`; and the strong min-max duality (4.7) holds, both sides attained at
the common value `R(π*, W*)`:
`max_{π ∈ Π} min_{W ∈ 𝒲} R(π, W) = R(π*, W*) = min_{W ∈ 𝒲} max_{π ∈ Π} R(π, W)`.

The paper states (4.6) for every solution `(π*, W*)` with `π*` deterministic. That reading is false
(a two-state counterexample in which every policy is robust-optimal but the first action is not
nominally optimal against the chosen `W*`; see the mission's moderation notes). We state that some
solution with `π*` deterministic satisfies (4.6), which is what the proof of Theorem 5.1 uses. -/
theorem theorem_4_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    ∃ (πs : S → A → ℝ) (Ws : Fin r → S → ℝ), IsDeterministic πs ∧
      M.IsRobustSolution lam πs Ws ∧
      IsGreatest ((fun π => M.R lam π Ws) '' Policies S A) (M.R lam πs Ws) ∧
      IsGreatest (M.z lam '' Policies S A) (M.R lam πs Ws) ∧
      IsLeast (M.maxR lam '' M.Wset) (M.R lam πs Ws) := by sorry

end FactorRMDP.ValueIter
