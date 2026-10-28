-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ShortestExchangeAugmentation_shortest_exchange_augmentation
-- name    : CountingMatroid.Analysis.ShortestExchangeAugmentation.shortest_exchange_augmentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:41:40.611995+00:00
-- url     : https://prove2.me/theorems/947d41df-2a15-4f67-a917-a22f49066817
-- title:
--   A globally shortest exchange walk augments a common independent set
-- statement:
--   Let $M_1,M_2$ be matroids with full ground set $[n]=\{0,\ldots,n-1\}$, and let $o_1,o_2$ exactly decide their independence predicates. Let $I\subseteq[n]$ be independent in both matroids. In the oracle-built exchange graph, sources are $v\notin I$ for which $I\cup\{v\}$ is independent in $M_1$, and sinks are those for which it is independent in $M_2$. An edge from $u\in I$ to $v\notin I$ exists exactly when $I-u+v$ is independent in $M_1$; an edge from $u\notin I$ to $v\in I$ exists exactly when $I-v+u$ is independent in $M_2$.
--
--   Let $p$ be a list carrying a shortest certificate: it records a source-to-sink walk in reverse order (sink at its head, source at its last entry), has no repeated vertices, has length at most $n$, and has length no greater than any source-to-sink walk. Starting from $I$, toggle each vertex of $p$ in list order, deleting it if present and inserting it otherwise; call the result $J$. Then
--   $$J\text{ is independent in }M_1\text{ and }M_2,\qquad |J|=|I|+1.$$
--   This is the mathematical augmentation guarantee, separated from the executable path search and its charges.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ShortestExchangeAugmentation.lean#L20-L100

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

namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
set_option autoImplicit false

/-! Mathematical half of augmentation: this file does not mention findPath or
its BFS tables. Global shortestness rules out the shortcuts needed in the
simultaneous-exchange argument. Fundamental-circuit induction establishes
independence for the first matroid, graph reversal establishes it for the second,
and alternating membership establishes the cardinality increment. -/
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Analysis.ExchangeWalkReversal
open scoped symmDiff

theorem CountingMatroid.Analysis.ShortestExchangeAugmentation.shortest_exchange_augmentation {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hc : ShortestCertificate (buildGraph o₁ o₂ I).val p) :
    let next := p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by sorry
