-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkCardinality_augmenting_walk_cardinality
-- name    : CountingMatroid.Analysis.ExchangeWalkCardinality.augmenting_walk_cardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:40:40.303506+00:00
-- url     : https://prove2.me/theorems/2ae79f3f-8dd3-4596-b3dc-4349377964d7
-- title:
--   Toggling a simple augmenting walk increases cardinality by one
-- statement:
--   Let $n\in\mathbb N$, let $M_1,M_2$ be matroids on $[n]$, and let $o_1,o_2$ be exact independence oracles for them. Let $I\subseteq[n]$ and build its directed exchange graph: sources are elements $v\notin I$ with $I\cup\{v\}$ independent in $M_1$, and sinks satisfy the analogous $M_2$ condition. An edge from an inside vertex to an outside vertex tests the corresponding $M_1$ exchange; the reverse membership orientation tests the corresponding $M_2$ exchange. Let $p$ be a source-to-sink walk, stored in reverse order, with no repeated vertices. Toggle membership in $I$ once for each listed vertex, obtaining $J$. Then
--   $$|J|=|I|+1.$$
--   No assumption that $I$ is common independent is included.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeWalkCardinality.lean#L104-L122

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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

namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace Arlib
end Arlib
set_option autoImplicit false

/-! Cardinality of the symmetric difference with a simple alternating
source-to-sink exchange walk. This argument uses no matroid exchange theorem. -/
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

theorem CountingMatroid.Analysis.ExchangeWalkCardinality.augmenting_walk_cardinality {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) (p : List (Fin n))
    (hw : AugmentingWalk (buildGraph o₁ o₂ I).val p) (hp : p.Nodup) :
    (p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I).card =
      I.card + 1 := by sorry
