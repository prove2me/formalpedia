-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_intersectionSolver_correct
-- name    : CountingMatroid.Analysis.FeasibilitySolver.intersectionSolver_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:44:40.029526+00:00
-- url     : https://prove2.me/theorems/bced9bf2-518f-47d5-a061-bc5abd42b3cf
-- title:
--   The capped intersection solver decides common independence at a prescribed size
-- statement:
--   Let $n,r\in\mathbb N$ and let $M_1,M_2$ be matroids with full ground $[n]$. Let $o_1,o_2$ return their exact independence predicates on Boolean subset queries. The concrete intersection solver starts from the empty set, performs $r$ exchange-graph augmentation rounds, and tests whether the final cardinality is $r$. Its returned Boolean satisfies
--
--   $$\operatorname{intersectionSolver}(n,r,o_1,o_2)=\operatorname{true}\quad\Longleftrightarrow\quad\exists I\subseteq[n]:\ |I|=r,\ I\text{ independent in both }M_1,M_2.$$
--
--   No common-rank hypothesis is required; $r$ is a requested size and may exceed the maximum common independent size.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FeasibilitySolver.lean#L170-L246

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
import Definitions.Def_CountingMatroid_Analysis_FeasibilitySolver
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
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

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
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
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver
end CountingMatroid.Analysis.FeasibilitySolver
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

theorem CountingMatroid.Analysis.FeasibilitySolver.intersectionSolver_correct (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) :
    (IntersectionSearch.intersectionSolver.run n r o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by sorry
