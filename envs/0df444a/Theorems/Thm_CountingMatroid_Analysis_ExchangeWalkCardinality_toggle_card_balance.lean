-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkCardinality_toggle_card_balance
-- name    : CountingMatroid.Analysis.ExchangeWalkCardinality.toggle_card_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:50:52.854432+00:00
-- url     : https://prove2.me/theorems/8fe05351-faf3-4d7e-9d6f-0e66010ae81e
-- title:
--   Cardinality balance for a list of distinct set toggles
-- statement:
--   Let $n\in\mathbb N$, let $I\subseteq[n]=\{0,\ldots,n-1\}$, and let $p$ be a finite list of distinct indices. Starting from $I$, toggle each listed index in order: remove it when present and insert it when absent. Let $J$ be the resulting set, and let $N_{\rm in}$ and $N_{\rm out}$ count the entries of $p$ that respectively belong and do not belong to the original set $I$. Then
--
--   $$|J|+N_{\rm in}=|I|+N_{\rm out}.$$
--
--   Distinctness ensures that each entry contributes exactly one removal or insertion according to its original membership.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeWalkCardinality.lean#L11-L58

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

theorem CountingMatroid.Analysis.ExchangeWalkCardinality.toggle_card_balance {n : ℕ} (p : List (Fin n)) (I : Finset (Fin n))
    (hp : p.Nodup) :
    (p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I).card +
      (p.filter (fun i => decide (i ∈ I))).length =
    I.card + (p.filter (fun i => decide (i ∉ I))).length := by sorry
