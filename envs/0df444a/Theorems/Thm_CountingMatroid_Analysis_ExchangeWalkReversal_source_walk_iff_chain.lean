-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkReversal_source_walk_iff_chain
-- name    : CountingMatroid.Analysis.ExchangeWalkReversal.source_walk_iff_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:51:00.366213+00:00
-- url     : https://prove2.me/theorems/792d1806-3923-443a-a8f5-1b5327cf17e6
-- title:
--   Source walks are reverse adjacent-edge chains ending at a source
-- statement:
--   Let $g$ be a directed graph on $[n]$, with a Boolean edge predicate and designated source and sink flags, and let $p$ be a list of vertices. The inductively defined source-walk predicate starts with a singleton source and prepends $v$ to a walk headed by $u$ whenever $u\to v$ is an edge. Then
--
--   $$\operatorname{SourceWalk}_g(p)\quad\Longleftrightarrow\quad \bigl[\text{each adjacent pair }(v,u)\text{ in }p\text{ has }u\to v\bigr]\ \land\ \bigl[\text{the last entry of }p\text{ exists and is a source}\bigr].$$
--
--   This identifies the reverse-list encoding with an ordinary directed walk read from its last entry to its first.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeWalkReversal.lean#L16-L44

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

namespace Arlib
end Arlib
set_option autoImplicit false

/-! Reversing an exchange graph interchanges its sources and sinks. Reverse
list paths then satisfy the same augmentation and shortestness predicates. -/
namespace CountingMatroid.Analysis.ExchangeWalkReversal
end CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

theorem CountingMatroid.Analysis.ExchangeWalkReversal.source_walk_iff_chain {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) :
    SourceWalk g p ↔
      p.IsChain (fun v u => g.edges u v = true) ∧
        ∃ v, p.getLast? = some v ∧ (g.terminals v).1 = true := by sorry
