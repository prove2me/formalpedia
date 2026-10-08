-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_negative_cycle_criterion_mcfp0
-- name    : DiscreteConvex.NetworkFlowsB.negative_cycle_criterion_mcfp0
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:36:41.43755+00:00
-- url     : https://prove2.me/theorems/7981606a-6a52-4531-b870-6af7da38729a
-- title:
--   Theorem 9.5 -- negative_cycle_criterion_mcfp0
-- statement:
--   **Theorem 9.5** (Negative-cycle criterion; p.252). For a feasible flow $\xi$ to the minimum cost flow problem MCFP0, $\xi$ is optimal iff the auxiliary network $(G_\xi,\ell_\xi)$ of Eq. (9.34) has no negative cycle.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, Theorem 9.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, Theorem 9.5

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.5 (Negative-cycle criterion; p.252). For a feasible flow `ξ` to MCFP0, `ξ` is
optimal iff the auxiliary network `(Gξ, ℓξ)` has no negative cycle. -/
theorem negative_cycle_criterion_mcfp0 (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (hfeas : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi) :
    OptimalFlowMCFP0 tail head cUpper cLower gamma x xi ↔
      ¬ HasNegativeCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head)
        (AuxActiveMCFP0 cUpper cLower xi) (AuxLengthMCFP0 gamma) := by sorry

end DiscreteConvex.NetworkFlowsB
