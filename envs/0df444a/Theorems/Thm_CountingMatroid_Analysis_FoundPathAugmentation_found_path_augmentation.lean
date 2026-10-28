-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FoundPathAugmentation_found_path_augmentation
-- name    : CountingMatroid.Analysis.FoundPathAugmentation.found_path_augmentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:42:39.667244+00:00
-- url     : https://prove2.me/theorems/5d3c1cb3-1254-470d-bcde-6d2f90c6fdba
-- title:
--   The path returned by exchange search augments common independence
-- statement:
--   Let $n\in\mathbb N$, let $M_1,M_2$ be matroids with full ground $[n]$, and let $o_1,o_2$ decide their independence predicates exactly. Let $I\subseteq[n]$ be independent in both matroids. For a current set $I\subseteq[n]$, the exchange graph has sources $e\notin I$ with $I+e$ independent in $M_1$, sinks $e\notin I$ with $I+e$ independent in $M_2$, arcs $u\to v$ from $u\in I$ to $v\notin I$ when $I-u+v$ is independent in $M_1$, and arcs from $u\notin I$ to $v\in I$ when $I-v+u$ is independent in $M_2$. The program builds this graph through the two oracles and uses synchronous breadth-first layers, storing paths in reverse order, before selecting a shortest recorded sink path. Suppose the search returns a list $p$. Starting from $I$, toggle membership of each entry of the first $n$ entries of $p$, and call the result $I'$. Then
--
--   $$I'\in\mathcal I(M_1)\cap\mathcal I(M_2),\qquad |I'|=|I|+1.$$
--
--   The conclusion concerns the shortest path actually returned by the program, not an arbitrary directed walk.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FoundPathAugmentation.lean#L22-L78

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
set_option autoImplicit false

/-!
The successful branch of the concrete exchange search. Correctness requires
both the algorithmic fact that the selected reverse path is shortest and the
matroid fact that toggling a shortest exchange path augments independence.
The explicit ShortestCertificate separates these obligations. The parent now
composes the two child statements; both children remain open proof obligations.
The checked value bridge removes operation charges and the certified length
bound removes the cap. Arbitrary directed paths do not satisfy the conclusion.
-/

namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FoundPathAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

theorem CountingMatroid.Analysis.FoundPathAugmentation.found_path_augmentation {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hp : (findPath (buildGraph o₁ o₂ I).val).val = some p) :
    let next := (Arlib.Computation.Charged.foldl toggle (p.take n) I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by sorry
