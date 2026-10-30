-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_proposition_3_2
-- name    : BrownSharedSignals.Fluid.proposition_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:48.444181+00:00
-- url     : https://prove2.me/theorems/c8872fb6-3973-4eb3-971d-81e12489d68b
-- title:
--   Proposition 3.2 — LP duality and the independent occupancy policy
-- statement:
--   The history-dependent Lagrangian LP (6) and occupancy LP (7) attain their optima and have the same value, equal to the optimum over nonnegative history-dependent multipliers. For any optimal LP (6) multiplier and project-coordinate solution, any optimal LP (7) occupancy, and any independent policy obtained by normalized occupancy with distribution-valued null-state completions:
--
--   (a) The policy attains the Lagrangian optimum from the specified initial state.
--
--   (b) At every local state and signal history, a uniquely optimal local Lagrangian action is selected with probability one, and every strictly suboptimal action is selected with probability zero. This universal state claim is retained even at zero occupancy; the source issue is recorded separately.
--
--   (c) At every period and rooted signal history, the expected resource consumption $C_t$ satisfies
--   $$C_t\le B_t(z_t),\qquad \lambda_t^*(h_t)\ge0,\qquad \lambda_t^*(h_t)(B_t(z_t)-C_t)=0.$$
--   The conditional expectation uses the specified fixed-history kernel, including null histories. No feasibility, attainment or action-support conclusion is assumed as an extra hypothesis.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - encoding: conditioning on every rooted signal history → the forward project kernel along the fixed signal path, also on probability-zero histories; reason: this explicitly chooses a conditional-kernel version without adding a positive-history-probability assumption or removing null histories
--   - encoding: optimal values and arbitrary optimal solutions of LPs (6) and (7) → attainment and equality to the history-Lagrangian optimum are explicit conclusions; reason: these are the optimization semantics stated in Section 3 and used in the complete proposition
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Proposition 3.2, printed 16 / PDF 17

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem proposition_3_2 {N T : ℕ} (M : Model N T) :
    (∃ lam ℓ, LP6Optimal M lam ℓ) ∧ (∃ μ, LP7Optimal M μ) ∧
    LP6Value M = LP7Value M ∧ LP6Value M = optimalRelaxation M ∧
    ∀ lam ℓ μ, LP6Optimal M lam ℓ → LP7Optimal M μ →
    ∀ p : LocalPolicy M, OccupancyPolicy M μ p →
      penalizedPolicyAux M lam (independentPolicy M p) T 0 (initialHistory M) M.initialState =
        lagrangian M lam 0 (initialHistory M) M.initialState ∧
      (∀ t < T, ∀ h i s (a : Action M t i s (current M h)),
        ((∀ b : Action M t i s (current M h), b ≠ a →
            localActionValue M lam (projectValue M lam) t h i s b <
            localActionValue M lam (projectValue M lam) t h i s a) → p t h i s a = 1) ∧
        (localActionValue M lam (projectValue M lam) t h i s a < projectValue M lam t h i s →
          p t h i s a = 0)) ∧
      (∀ t < T, ∀ h, h 0 = M.initialSignal →
        let C := conditionalActionExpectation M (independentPolicy M p) t h
          (fun s a => consumption M t s (current M h) (actionVector M a))
        C ≤ M.budget t (current M h) ∧ 0 ≤ lam t h ∧
          lam t h * (M.budget t (current M h) - C) = 0) := by sorry

end BrownSharedSignals.Fluid
