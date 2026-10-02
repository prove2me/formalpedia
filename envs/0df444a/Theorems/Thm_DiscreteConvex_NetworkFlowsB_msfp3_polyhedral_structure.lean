-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsB_msfp3_polyhedral_structure
-- name    : DiscreteConvex.NetworkFlowsB.msfp3_polyhedral_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:36:54.745828+00:00
-- url     : https://prove2.me/theorems/1d555638-366f-4328-805e-e4c6e28f725d
-- title:
--   Theorem 9.15 -- msfp3_polyhedral_structure
-- statement:
--   **Theorem 9.15** (p.261). Suppose MSFP3 has an optimal solution. (1) The set of boundaries of optimal flows $\partial\Xi^*$ is an M2-convex polyhedron and the set of optimal potentials $\Pi^*$ is an L-convex polyhedron. (2) Primal integrality: with domain-integer arc and boundary costs, $\partial\Xi^*$ is an integral M2-convex polyhedron and an integer-valued optimal flow exists. (3) Dual integrality: with dual-integer arc and boundary costs, $\Pi^*$ is an integral L-convex polyhedron and an integer-valued optimal potential exists.
--
--   **Formalization note.** "Primal integral" (the book's $C[Z|R\to R]$/$M[Z|R\to R]$ notation) is formalized as integer effective domain (`IsDomainIntegerArc`/`IsDomainIntegerR`); "dual integral" ($C[R\to R|Z]$/$M[R\to R|Z]$) is formalized as the existence of an integer subgradient at every domain point (`IsDualIntegralArc`/`IsDualIntegralR`), a standard equivalent characterization for polyhedral convex functions. See MODERATION_NOTES.md.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, Theorem 9.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, Theorem 9.15

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.15 (p.261). If MSFP3 has an optimal solution: (1) the set of boundaries of
optimal flows is an M2-convex polyhedron and the set of optimal potentials is an L-convex
polyhedron; (2) primal integrality: with domain-integer data, the former is an integral
M2-convex polyhedron and an integer-valued optimal flow exists; (3) dual integrality: with
dual-integer data, the latter is an integral L-convex polyhedron and an integer-valued optimal
potential exists. Clause (1) is in the real classes `M⁰₂[R]` and `L⁰[R]`; integrality is what
clauses (2) and (3) add, so the hull-of-an-integer-set classes would make (1) false already for
one arc of cost `1/2`. -/
theorem msfp3_polyhedral_structure (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (hfPoly : IsPolyhedralConvex f)
    (hfa : ∀ a, IsPolyhedralConvexArc (fa a))
    (hopt : ∃ xi, OptimalFlowMCFP3 tail head fa f xi) :
    M2ConvexPolyhedronR (BoundaryOptSetMSFP3 tail head fa f) ∧
    LConvexPolyhedronR (OptimalPotentialSetMSFP3 tail head fa f) ∧
    (((∀ a, IsDomainIntegerArc (fa a)) ∧ IsDomainIntegerR f) →
      IsIntegralPolyhedron (BoundaryOptSetMSFP3 tail head fa f) ∧
      ∃ xiZ : A → ℤ, OptimalFlowMCFP3 tail head fa f (fun a => (xiZ a : ℝ))) ∧
    (((∀ a, IsDualIntegralArc (fa a)) ∧ IsDualIntegralR f) →
      IsIntegralPolyhedron (OptimalPotentialSetMSFP3 tail head fa f) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMSFP3 tail head fa f) := by sorry

end DiscreteConvex.NetworkFlowsB
