-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_IntersectionAugmentation_augmentation_progress
-- name    : CountingMatroid.Analysis.IntersectionAugmentation.augmentation_progress
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:43:34.220522+00:00
-- url     : https://prove2.me/theorems/62837303-55dc-4f5f-ade6-009c48a3eb98
-- title:
--   An augmentation either grows common independence or certifies optimality
-- statement:
--   Let $M_1,M_2$ have full ground $[n]$, let $o_1,o_2$ be their exact independence oracles, and let $I\subseteq[n]$ be independent in both. For a current set $I\subseteq[n]$, the exchange graph has sources $e\notin I$ with $I+e$ independent in $M_1$, sinks $e\notin I$ with $I+e$ independent in $M_2$, arcs $u\to v$ from $u\in I$ to $v\notin I$ when $I-u+v$ is independent in $M_1$, and arcs from $u\notin I$ to $v\in I$ when $I-v+u$ is independent in $M_2$. The program builds this graph through the two oracles and uses synchronous breadth-first layers, storing paths in reverse order, before selecting a shortest recorded sink path. Let $I'$ be the result of one augmentation: toggle the capped returned path if one exists, otherwise retain $I$. Then $I'$ is common independent and
--
--   $$|I'|=|I|+1
--   \quad\text{or}\quad
--   \left(I'=I\ \land\
--   \forall J\in\mathcal I(M_1)\cap\mathcal I(M_2),\ |J|\le|I|\right).$$
--
--   Thus failure to augment certifies maximum cardinality, not merely inclusion maximality.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionAugmentation.lean#L59-L131

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
set_option autoImplicit false

/-!
The augmentation-progress proof combines exact exchange-query predicates,
a graph separator when search fails, and shortest-path exchange preservation
when search succeeds. The matroid basis certificates on both sides of the
separator are proved here using `ExchangeClosedBasis`. Graph-search saturation
is proved in `NoPathSeparator`; successful-path preservation remains an
explicit obligation in `FoundPathAugmentation`. This is an internal refinement
of the cited pretest, not an additional oracle or an assumed contract.
-/

namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

theorem CountingMatroid.Analysis.IntersectionAugmentation.augmentation_progress {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) :
    let next := (augmentOnce o₁ o₂ I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      (next.card = I.card + 1 ∨
        (next = I ∧ ∀ J : Finset (Fin n),
          M₁.Indep (J : Set (Fin n)) → M₂.Indep (J : Set (Fin n)) → J.card ≤ I.card)) := by sorry
