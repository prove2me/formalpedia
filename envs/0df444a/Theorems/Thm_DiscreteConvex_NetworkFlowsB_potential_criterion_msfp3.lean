-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_potential_criterion_msfp3
-- name    : DiscreteConvex.NetworkFlowsB.potential_criterion_msfp3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:32:57.743809+00:00
-- url     : https://prove2.me/theorems/fd9dca50-4ff6-46d3-aa0c-4a6d2c7fca2a
-- title:
--   Theorem 9.14 -- potential_criterion_msfp3
-- statement:
--   **Theorem 9.14** (Potential criterion for MSFP3; p.260). Immediate from Theorem 9.4, since the M-convex submodular flow problem MSFP3 is the special case of MCFP3 with M-convex boundary cost $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.260, Theorem 9.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.260, Theorem 9.14

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.14 (Potential criterion for MSFP3; p.260). Immediate from Theorem 9.4, since
MSFP3 is the special case of MCFP3 with M-convex boundary cost `f`. -/
theorem potential_criterion_msfp3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (hfPoly : IsPolyhedralConvex f)
    (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by sorry

end DiscreteConvex.NetworkFlowsB
