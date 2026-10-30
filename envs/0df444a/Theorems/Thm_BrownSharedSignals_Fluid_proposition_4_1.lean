-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_proposition_4_1
-- name    : BrownSharedSignals.Fluid.proposition_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:54:00.280992+00:00
-- url     : https://prove2.me/theorems/1c8e8c87-208a-410a-9884-ceaa26ef274e
-- title:
--   Proposition 4.1 — Concavity, piecewise linearity and supergradients
-- statement:
--   At each period and current signal, the dynamic fluid value is concave and is a finite minimum of affine functions on the full product of local probability simplexes. Given finite affine representations of the next-period values, the Bellman optimization is exactly LP (EC-2), with attained primal and dual (EC-3) optima. For any fluid state $f$, the Bellman control maximum is attained and equals the LP value. Every optimal dual point has the same objective as the fluid value, and its mass-constraint vector $\theta$ satisfies
--   $$V_t^F(g,z)\le V_t^F(f,z)+\sum_{i,s}\theta_i(s)(g_i(s)-f_i(s))$$
--   for every other fluid state $g$. The state domain is continuous; no finite grid is introduced.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: maximization LP (EC-2) and its dual → EC-2 is represented by the published minimization LP API using the negative objective, with the explicit EC-3 dual kept in source orientation; reason: negating the objective changes no feasible point and preserves the source optimal value after negation
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Proposition 4.1, printed 18 / PDF 19

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem proposition_4_1 {N T : ℕ} (M : Model N T) :
    (∀ t, t ≤ T → ∀ z,
      ConcaveOn ℝ {f | IsFluidState M f} (fun f => fluidValue M t f z) ∧
      ∃ K : AffinePieces M, Represents M t z K) ∧
    (∀ t < T, ∀ z (K : Signal M → AffinePieces M),
      (∀ z', Represents M (t+1) z' (K z')) →
      ∀ f, IsFluidState M f →
        (∃ u, ControlOptimal M t f z u ∧ fluidValue M t f z = fluidActionValue M t z u) ∧
        fluidValue M t f z = EC2Value M t f z K ∧
        (∃ x, LinearOptimization.IsLpOptimal (EC2LP M t f z K).c
          (LinearOptimization.generalFeasibleSet (EC2LP M t f z K)) x) ∧
        (∃ d, EC3Optimal M t f z K d) ∧
        (∀ d, EC3Optimal M t f z K d →
          EC3Objective M t f z K d = fluidValue M t f z ∧
          Supergradient M t z f d.theta)) := by sorry

end BrownSharedSignals.Fluid
