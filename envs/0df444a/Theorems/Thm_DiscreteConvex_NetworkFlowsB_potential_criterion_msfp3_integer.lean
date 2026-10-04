-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_potential_criterion_msfp3_integer
-- name    : DiscreteConvex.NetworkFlowsB.potential_criterion_msfp3_integer
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:37:21.876094+00:00
-- url     : https://prove2.me/theorems/9e271f47-9634-4d1a-916a-847a83eda35a
-- title:
--   Theorem 9.16 -- potential_criterion_msfp3_integer
-- statement:
--   **Theorem 9.16** (Potential criterion, integer flows; p.262). Consider MSFP3 with integer flows and M-convex $f:\mathbb Z^V\to\mathbb R$. (1)-(2) the OPT/POT equivalence and its potential-invariance, as in Theorem 9.14. (3) The set of boundaries of optimal integer flows is M2-convex. (4) With integer-valued cost data, an integer-valued optimal potential exists and the set of all integer-valued optimal potentials is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsB_DiscreteConvexArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.16 (Potential criterion, integer flows; p.262). Consider MSFP3 with integer
flows and M-convex `f : Zⱽ → R`. (1)-(2) the OPT/POT equivalence and its potential-invariance, as
in Theorem 9.14; (3) the set of boundaries of optimal integer flows is M2-convex; (4) with
integer-valued cost data and an optimal flow, an integer-valued optimal potential exists and the
set of all integer-valued optimal potentials is L-convex. The arc costs lie in the book's class
`C[Z→R]`: with one arc, `f` the indicator of `0` and `fa(t) = -t²`, the zero flow is optimal
while no potential puts `0` in `arg min (fa + δp)`, so (OPT) held and (POT) failed. Part (4)
asserts that an optimal flow exists, so it must assume one. -/
theorem potential_criterion_msfp3_integer (tail head : A → V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hfa : ∀ a, DiscreteConvexArcZ (fa a)) :
    (∀ xi, FeasibleFlowMSFP3Z tail head fa f xi →
      (OptimalFlowMSFP3Z tail head fa f xi ↔
        ∃ p : V → ℝ, IsOptimalPotentialZ tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMSFP3Z tail head fa f xi → IsOptimalPotentialZ tail head fa f xi p →
      ∀ xi', FeasibleFlowMSFP3Z tail head fa f xi' →
        (OptimalFlowMSFP3Z tail head fa f xi' ↔ IsOptimalPotentialZ tail head fa f xi' p)) ∧
    M2ConvexSet (BoundaryOptSetMSFP3Z tail head fa f) ∧
    (((∀ a, IsIntegerValuedArcZ (fa a)) ∧ IsIntegerValuedFn f ∧
        (∃ xi, OptimalFlowMSFP3Z tail head fa f xi)) →
      (∃ pZ : V → ℤ, ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧
        IsOptimalPotentialZ tail head fa f xi (fun v => (pZ v : ℝ))) ∧
      LConvexSet (OptimalPotentialSetZ tail head fa f)) := by sorry

end DiscreteConvex.NetworkFlowsB
