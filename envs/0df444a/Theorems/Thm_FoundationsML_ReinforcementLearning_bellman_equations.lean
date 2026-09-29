-- Prove2me | Theorems.Thm_FoundationsML_ReinforcementLearning_bellman_equations
-- name    : FoundationsML.ReinforcementLearning.bellman_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:38:02.035993+00:00
-- url     : https://prove2.me/theorems/cbd5ee3f-a2a4-4c83-b26d-eca3dec85f6d
-- title:
--   Proposition 17.9 — Bellman equations
-- statement:
--   **Statement (Proposition 17.9, p. 385, PDF p. 402, eq. (17.5)).** The values $V_\pi(s)$ of
--   policy $\pi$ at states $s\in S$ for an infinite horizon MDP obey the following system of
--   linear equations:
--   $$\forall s\in S,\quad V_\pi(s) = \mathbb E_{a_1\sim\pi(s)}[r(s,a_1)] + \gamma\sum_{s'}
--     P[s'\mid s,\pi(s)]\,V_\pi(s').$$
--
--   This is the key milestone for the mission's goal (Theorem 17.10): it shows the policy value
--   function satisfies a genuine system of *linear* equations (unlike the non-linear Bellman
--   optimality equations (17.4)), which the goal then shows admits a unique closed-form solution.
--
--   **Formalization Note.** The right-hand side's expectation and transition terms are written
--   via `InducedReward`/`InducedTransition`, the mixed-action marginalizations of `Er`/`P` under
--   `π(s)`, matching the book's own notation `R_s`/`P_{s,s'}` used immediately after (17.5) to
--   rewrite the system in matrix form (17.6).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 385, Proposition 17.9 (PDF p. 402)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

namespace FoundationsML.ReinforcementLearning

/-- Proposition 17.9 (Bellman equations; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 385, PDF p. 402). The values `V_π(s)` of policy
`π` at states `s ∈ S` for an infinite horizon MDP obey the following system of linear equations:
`∀ s ∈ S, V_π(s) = E_{a1∼π(s)}[r(s,a1)] + γ ∑_{s'} P[s'|s,π(s)] V_π(s')`.

**Formalization Note.** The right-hand side's expectation and transition terms are written via
`InducedReward`/`InducedTransition`, the mixed-action marginalizations of `Er`/`P` under `π(s)`,
matching (17.5)/(17.6)'s own notation `R_s`/`P_{s,s'}`. -/
theorem bellman_equations {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ s : S, PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by sorry

end FoundationsML.ReinforcementLearning
