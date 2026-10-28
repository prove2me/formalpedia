-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_rankOneGuard_bounded
-- name    : CountingMatroid.Analysis.FeasibilitySolver.rankOneGuard_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:08:46.829195+00:00
-- url     : https://prove2.me/theorems/368555ae-c795-4385-afd6-f6b2955daaaf
-- title:
--   A rank-one guard preserves uniform polynomial charged bounds
-- statement:
--   Let $S$ be a feasibility implementation taking $n,r\in\mathbb N$ and two arbitrary Boolean subset-oracle functions. Let $C_o,d_o,C_s,d_s\in\mathbb N$. Suppose every input satisfies
--
--   $$\operatorname{oracleCalls}(S)\le C_o(n+r+1)^{d_o},\qquad \operatorname{otherSteps}(S)\le C_s(n+r+1)^{d_s}.$$
--
--   The rank-one guard first tests whether $r=1$, uses the singleton scan in that case, and otherwise calls $S$. Its uniform bounds are
--
--   $$\operatorname{oracleCalls}(\operatorname{guard}_1S)\le(C_o+2)(n+r+1)^{d_o+3},$$
--   $$\operatorname{otherSteps}(\operatorname{guard}_1S)\le(C_s+5)(n+r+1)^{d_s+3}.$$
--
--   The nonoracle counter sums charged fair-bit and named primitive instructions. The resource bounds impose no correctness promise on either oracle.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FeasibilitySolver.lean#L128-L168

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

theorem CountingMatroid.Analysis.FeasibilitySolver.rankOneGuard_bounded (solver : FeasibilityImplementation)
    (callConstant callDegree bitConstant bitDegree : ℕ)
    (hbounded : FeasibilityBounded solver callConstant callDegree bitConstant bitDegree) :
    FeasibilityBounded (rankOneGuard solver)
      (callConstant + 2) (callDegree + 3) (bitConstant + 5) (bitDegree + 3) := by sorry
