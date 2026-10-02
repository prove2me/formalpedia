-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_unique_min_for_cycle_cancellation
-- name    : DiscreteConvex.NetworkFlowsC.unique_min_for_cycle_cancellation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T03:11:34.428211+00:00
-- url     : https://prove2.me/theorems/4e0971d9-b39b-42c5-bf67-e978a121f6d7
-- title:
--   Proposition 9.25 -- unique_min_for_cycle_cancellation
-- statement:
--   **Proposition 9.25** (p.267). $(\partial\xi,\partial\bar\xi)$ satisfies the unique-min condition, where $\bar\xi$ is the flow obtained from $\xi$ by canceling a smallest negative cycle (Theorem 9.22). This is the key fact used to prove Theorem 9.22.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.267, Proposition 9.25.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.267, Proposition 9.25

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_UniqueMinConditionPair
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FeasibleFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxActiveMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxLengthMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsSmallestNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ModifiedFlow

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Proposition 9.25 (p.267). `(∂ξ, ∂ξ̄)` satisfies the unique-min condition, where `ξ̄` is the
flow obtained from `ξ` by canceling a smallest negative cycle. -/
theorem unique_min_for_cycle_cancellation (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (xi : A → ℤ) (hfeas : FeasibleFlowMSFP2Z tail head cUpper cLower f xi) (k : ℕ)
    (a : Fin (k+1) → (A ⊕ A ⊕ (V × V)))
    (hsmallest : IsSmallestNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
      (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) k a) :
    UniqueMinConditionPair f (BoundaryZ tail head xi) (BoundaryZ tail head (ModifiedFlow tail head k a xi)) := by sorry

end DiscreteConvex.NetworkFlowsC
