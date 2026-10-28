-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_GreedyRankCorrect_greedyRank_eq_eRk
-- name    : CountingMatroid.Analysis.GreedyRankCorrect.greedyRank_eq_eRk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:51:14.714984+00:00
-- url     : https://prove2.me/theorems/bc7e2a1a-02de-49cb-925f-7b4f9137f411
-- title:
--   Greedy oracle scan computes matroid rank
-- statement:
--   Let $M$ be a matroid with full ground $[n]$, and let $o$ be an exact Boolean independence oracle. For a subset $A\subseteq[n]$, the greedy scan visits ground elements in order, inserting an element of $A$ whenever independence is preserved and maintaining its selected-set count. For either Boolean charge label $\mathrm{which}$,
--
--   $$\operatorname{value}(\mathrm{greedyRank}(\mathrm{which},o,A))=r_M(A).$$
--
--   The formal equality casts the natural output into the extended-natural rank type. The charge label selects the oracle accounting category and does not change the computed rank.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/GreedyRankCorrect.lean#L9-L133

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
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

namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.GreedyRankCorrect

open CountingMatroid.Model

theorem CountingMatroid.Analysis.GreedyRankCorrect.greedyRank_eq_eRk {n : ℕ} (M : Matroid (Fin n))
    (o : IndependenceOracle n) (hfull : M.E = Set.univ)
    (hexact : ExactOracle M o) (which : Bool) (A : Finset (Fin n)) :
    ((CountingMatroid.Model.Subroutines.greedyRank which o A).val : ℕ∞) =
      M.eRk (A : Set (Fin n)) := by sorry
