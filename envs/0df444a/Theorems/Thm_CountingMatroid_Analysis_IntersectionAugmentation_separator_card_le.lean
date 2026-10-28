-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_IntersectionAugmentation_separator_card_le
-- name    : CountingMatroid.Analysis.IntersectionAugmentation.separator_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:52:06.398982+00:00
-- url     : https://prove2.me/theorems/87dc9621-0485-4d21-a9b9-6b327a477bd1
-- title:
--   Complementary basis certificates bound common independent sets
-- statement:
--   Let $M_1,M_2$ be matroids on the finite ambient set $[n]$, and let $I,R\subseteq[n]$. Assume $I\setminus R$ is a basis of $[n]\setminus R$ in $M_1$, and $I\cap R$ is a basis of $R$ in $M_2$. Then every set $J$ independent in both matroids satisfies
--
--   $$|J|\le|I|.$$
--
--   No assumption that $I$ itself is common independent or that the matroids have full ground is required beyond the two basis certificates.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionAugmentation.lean#L23-L57

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

theorem CountingMatroid.Analysis.IntersectionAugmentation.separator_card_le {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (I R : Finset (Fin n))
    (hfirst : M₁.IsBasis ((I \ R : Finset (Fin n)) : Set (Fin n))
      ((Finset.univ \ R : Finset (Fin n)) : Set (Fin n)))
    (hsecond : M₂.IsBasis ((I ∩ R : Finset (Fin n)) : Set (Fin n))
      (R : Set (Fin n)))
    (J : Finset (Fin n)) (hJ₁ : M₁.Indep (J : Set (Fin n)))
    (hJ₂ : M₂.Indep (J : Set (Fin n))) : J.card ≤ I.card := by sorry
