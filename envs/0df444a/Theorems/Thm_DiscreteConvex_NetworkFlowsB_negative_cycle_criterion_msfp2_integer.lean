-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_negative_cycle_criterion_msfp2_integer
-- name    : DiscreteConvex.NetworkFlowsB.negative_cycle_criterion_msfp2_integer
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:37:14.498893+00:00
-- url     : https://prove2.me/theorems/25a32c21-9c87-4188-b9f5-3467f4d78537
-- title:
--   Theorem 9.20 -- negative_cycle_criterion_msfp2_integer
-- statement:
--   **Theorem 9.20** (Negative-cycle criterion, integer flows; p.264). For a feasible integer flow $\xi$ to the M-convex submodular integer flow problem MSFP2 with integer capacities and M-convex $f:\mathbb Z^V\to\mathbb R$, $\xi$ is optimal iff the auxiliary network $(G_\xi,\ell_\xi)$ of Eq. (9.74) has no negative cycle.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Theorem 9.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Theorem 9.20

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.20 (Negative-cycle criterion, integer flows; p.264). For a feasible integer flow
`ξ` to the M-convex submodular integer flow problem MSFP2 with integer capacities and M-convex
`f : Zⱽ → R`, `ξ` is optimal iff the auxiliary network `(Gξ, ℓξ)` of Eq. (9.74) has no negative
cycle. -/
theorem negative_cycle_criterion_msfp2_integer (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) (xi : A → ℤ)
    (hfeas : FeasibleFlowMSFP2Z tail head cUpper cLower f xi) :
    OptimalFlowMSFP2Z tail head cUpper cLower gamma f xi ↔
      ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
        (AuxActiveMSFP2Z tail head cUpper cLower f xi) (AuxLengthMSFP2Z tail head gamma f xi) := by sorry

end DiscreteConvex.NetworkFlowsB
