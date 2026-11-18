-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_coordinate_geometry
-- name    : AlgebraicFPT.HittingSet.coordinate_geometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:11:24.434632+00:00
-- url     : https://prove2.me/theorems/a6dcb136-0ff8-414a-9843-42c29538db29
-- title:
--   Coordinate components and their Krull codimensions
-- statement:
--   Let $E$ be any finite hypergraph on $V=\{0,\ldots,n-1\}$. Let $I_E$ be its squarefree edge ideal over $\mathbb C$, and let $L_C$ be the subspace on which the coordinates indexed by $C$ vanish. Then
--
--   $$
--   L_C\in\operatorname{Irr}(\mathcal V(I_E))
--   \quad\Longleftrightarrow\quad C\text{ is an inclusion-minimal hitting set of }E,
--   \qquad \operatorname{codim}L_C=|C|.
--   $$
--
--   Moreover, $C\mapsto L_C$ is a bijection from all inclusion-minimal hitting sets onto the entire irreducible-component collection. These statements include empty vertex sets, empty hyperedge families, and empty hyperedges.
--
--   This identifies the combinatorial certificates represented by all components of the edge variety, with their actual Krull codimensions. It is the geometric correspondence used before Theorem 3.2.
-- source:
--   Liming Cai and Sixiang Zhang, Toward Algebraic Geometry of Fixed-Parameter Tractability: Case Studies, STOC 2027 submission #1035, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1035.pdf, §3, p.4 (component correspondence and codimension).

import Definitions.Def_AlgebraicFPT_HittingSet_Model
import Definitions.Def_HSElemKernel_HSInstance

set_option autoImplicit false

theorem AlgebraicFPT.HittingSet.coordinate_geometry (n : ℕ) (E : Finset (Finset (Fin n))) :
    (∀ C : Finset (Fin n),
      (AlgebraicFPT.HittingSet.coordinateSubspace C ∈
        AlgebraicFPT.HittingSet.components (AlgebraicFPT.HittingSet.edgeVariety E) ↔
        AlgebraicFPT.HittingSet.IsMinimalHitting E C)) ∧
    (∀ C : Finset (Fin n),
      AlgebraicFPT.HittingSet.HasCodim (AlgebraicFPT.HittingSet.coordinateSubspace C) C.card) ∧
    Set.BijOn AlgebraicFPT.HittingSet.coordinateSubspace
      {C | AlgebraicFPT.HittingSet.IsMinimalHitting E C}
      (AlgebraicFPT.HittingSet.components (AlgebraicFPT.HittingSet.edgeVariety E)) := by sorry
