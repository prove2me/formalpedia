-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_submodular_base_polyhedron_minkowski_sum
-- name    : DiscreteConvex.MConvexSetsB.submodular_base_polyhedron_minkowski_sum
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:35.185648+00:00
-- url     : https://prove2.me/theorems/85074162-8ebb-4f05-8791-6fab53e8fd6b
-- title:
--   Theorem 4.23 -- submodular_base_polyhedron_minkowski_sum
-- statement:
--   **Theorem 4.23** (p.115-116). (1) For submodular set functions $\rho_1,\rho_2 \in S[\mathbb R]$, $B(\rho_1) + B(\rho_2) = B(\rho_1+\rho_2)$ (Minkowski sum of base polyhedra). (2) For integer-valued $\rho_1,\rho_2 \in S[\mathbb Z]$, $(B(\rho_1)\cap\mathbb Z^V) + (B(\rho_2)\cap\mathbb Z^V) = B(\rho_1+\rho_2)\cap\mathbb Z^V$. (3) For M-convex sets $B_1,B_2 \subseteq \mathbb Z^V$, $B_1+B_2$ is an M-convex set and $\overline{B_1+B_2} = \overline{B_1}+\overline{B_2}$: the Minkowski sum of M-convex sets is again M-convex, and its convex hull is the Minkowski sum of the summands' convex hulls.
--
--   **Formalization Note.** Part (3) is stated for arbitrary M-convex $B_1, B_2$ independently of the $\rho_1,\rho_2$ of parts (1)-(2), rather than adding $B_i = B(\rho_i)\cap\mathbb Z^V$ as an extra hypothesis: Theorem 4.15 (chunk `04-mconvex-sets`) already supplies such a $\rho_i$ for any M-convex $B_i$, so no generality is lost by decoupling the three parts. Minkowski sums use Mathlib's pointwise `Set` addition.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115-116, Theorem 4.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115-116, Theorem 4.23

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
open scoped Pointwise

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.115-116, Theorem 4.23, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.23 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.115-116). See the item's
`natural_language_statement` for the full statement. -/
theorem submodular_base_polyhedron_minkowski_sum {V : Type*} [Fintype V] [DecidableEq V]
    (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1) (hρ2 : SubmodularSetFunction ρ2)
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) :
    (BasePolyhedron ρ1 + BasePolyhedron ρ2 = BasePolyhedron (fun X => ρ1 X + ρ2 X)) ∧
    (IsIntegerValued ρ1 → IsIntegerValued ρ2 →
      (BasePolyhedron ρ1 ∩ IntPts) + (BasePolyhedron ρ2 ∩ IntPts) =
        BasePolyhedron (fun X => ρ1 X + ρ2 X) ∩ IntPts) ∧
    (ExchangeAxiomB (B1 + B2) ∧ (B1 + B2).Nonempty ∧
      convexHull ℝ (IntEmbed (B1 + B2)) = convexHull ℝ (IntEmbed B1) + convexHull ℝ (IntEmbed B2)) := by sorry

end DiscreteConvex.MConvexSetsB
