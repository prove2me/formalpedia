-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ExchangeWalkCardinality_source_walk_card_balance
-- name    : CountingMatroid.Analysis.ExchangeWalkCardinality.source_walk_card_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:07:00.157253+00:00
-- url     : https://prove2.me/theorems/64b67302-0659-4cca-a1b1-9ce3d340fc6a
-- title:
--   Alternating source walks have a determined membership imbalance
-- statement:
--   Let $M_1,M_2$ be matroids on $[n]$ and let $o_1,o_2$ be exact Boolean independence oracles. Fix any subset $I\subseteq[n]$. In its exchange graph, sources are indices outside $I$ whose insertion is independent in $M_1$. An arc $u\to v$ either has $u\in I$, $v\notin I$, with $I-u+v$ independent in $M_1$, or has $u\notin I$, $v\in I$, with $I-v+u$ independent in $M_2$.
--
--   Let $p=v::\mathrm{tail}$ represent a source walk in reverse order: the last list entry is a source and adjacent entries follow directed edges when read from right to left. Counting entries with multiplicity,
--
--   $$\#\{i\text{ in }p:i\notin I\}=\#\{i\text{ in }p:i\in I\}+\begin{cases}0,&v\in I,\\1,&v\notin I.\end{cases}$$
--
--   The theorem does not require a simple walk or independence of $I$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeWalkCardinality.lean#L60-L102

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

theorem CountingMatroid.Analysis.ExchangeWalkCardinality.source_walk_card_balance {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) {p : List (Fin n)}
    (hw : SourceWalk (buildGraph o₁ o₂ I).val p) :
    ∀ v tail, p = v :: tail →
      (p.filter (fun i => decide (i ∉ I))).length =
        (p.filter (fun i => decide (i ∈ I))).length + (if v ∈ I then 0 else 1) := by sorry
