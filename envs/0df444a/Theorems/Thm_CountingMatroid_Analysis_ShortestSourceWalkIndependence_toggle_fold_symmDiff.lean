-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_toggle_fold_symmDiff
-- name    : CountingMatroid.Analysis.ShortestSourceWalkIndependence.toggle_fold_symmDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:51:46.668928+00:00
-- url     : https://prove2.me/theorems/cdcf032d-5b76-4fcc-9beb-f21bfd55ea6e
-- title:
--   Distinct membership toggles equal symmetric difference
-- statement:
--   Let $n\in\mathbb N$, let $I\subseteq[n]$, and let $p$ be a finite list of distinct elements of $[n]$. Starting from $I$, process $p$ in order, removing a listed element when present and inserting it when absent. If $J$ is the resulting set and $V(p)$ is the set of listed vertices, then
--   $$J=I\mathbin{\triangle}V(p),$$
--   where $\triangle$ denotes symmetric difference.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ShortestSourceWalkIndependence.lean#L45-L61

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
import Mathlib.Data.Finset.SymmDiff
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

namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace Arlib
end Arlib
set_option autoImplicit false

/-! The first-matroid half of shortest-path augmentation. Fundamental circuits
of later outside vertices avoid all earlier removed inside vertices, since such
membership would give a shorter source walk. -/
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open scoped symmDiff

theorem CountingMatroid.Analysis.ShortestSourceWalkIndependence.toggle_fold_symmDiff {n : ℕ} (I : Finset (Fin n)) (p : List (Fin n))
    (hp : p.Nodup) :
    p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I =
      I ∆ p.toFinset := by sorry
