-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_proposition_3_1
-- name    : BrownSharedSignals.Fluid.proposition_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:49.93754+00:00
-- url     : https://prove2.me/theorems/7ed805fe-9af2-4450-836f-3f53cd57fec9
-- title:
--   Proposition 3.1 — Weak duality and Lagrangian decomposition
-- statement:
--   For every finite shared-resource model and every nonnegative multiplier schedule depending on the full signal history, the optimal feasible value is at most the joint Lagrangian value at every period and state. Moreover,
--   $$L_t^\lambda(s,h)=\mathbb E[\sum_{\tau=t}^T\lambda_\tau(h_\tau)B_\tau(z_\tau)\mid h]+\sum_i L_{t,i}^\lambda(s_i,h).$$
--   The project values obey the local Bellman recursion with reward $r_{t,i}-\lambda_t b_{t,i}$, the actual local and signal transition laws, and zero terminal values. Both the weak-duality and decomposition assertions include the terminal period. The decomposition is asserted, not used as the definition of the joint relaxation.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Proposition 3.1, printed 11 / PDF 12

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem proposition_3_1 {N T : ℕ} (M : Model N T)
    (lam : Multiplier M) (hlam : NonnegativeMultiplier M lam) :
    (∀ t, t ≤ T → ∀ h s,
      optimalValue M t h s ≤ lagrangian M lam t h s ∧
      lagrangian M lam t h s = penalty M lam t h + ∑ i, projectValue M lam t h i (s i)) ∧
    (∀ t < T, ∀ h i s, projectValue M lam t h i s =
      sSup (Set.range fun a => localActionValue M lam (projectValue M lam) t h i s a)) ∧
    (∀ h i s, projectValue M lam T h i s = 0) := by sorry

end BrownSharedSignals.Fluid
