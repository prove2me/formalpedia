-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_TransversalRankBridge_transversal_rank_zero_iff_common_base
-- name    : CountingMatroid.Analysis.TransversalRankBridge.transversal_rank_zero_iff_common_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:44:27.542911+00:00
-- url     : https://prove2.me/theorems/01874a86-ca2c-44a2-bae7-d6b6b281a930
-- title:
--   Zero transversal deficiency characterizes common bases
-- statement:
--   Let $n,r\in\mathbb N$. Let $M_1,M_2$ be matroids with ground set $[n]$ and common rank $r$, and let $o_1,o_2$ be exact independence oracles for $M_1,M_2$. For any subset $A\subseteq[n]$, form $T(A)$ by selecting label zero on $A$ and label one on its complement. Then
--   $$n-\operatorname{pairedRank}(r,o_1,o_2,T(A))=0\quad\Longleftrightarrow\quad A\text{ is a base of both }M_1\text{ and }M_2,$$
--   where the subtraction on the left is truncated natural subtraction and paired rank is the value returned by the program’s rank scans.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TransversalRankBridge.lean#L11-L98

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
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

namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TransversalRankBridge

open CountingMatroid.Model

theorem CountingMatroid.Analysis.TransversalRankBridge.transversal_rank_zero_iff_common_base (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (A : Finset (Fin n)) :
    n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
      (Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A))))).val = 0 ↔
      A ∈ commonBases M₁ M₂ := by sorry
