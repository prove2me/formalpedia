-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankOneFeasibility_singletonScan_correct
-- name    : CountingMatroid.Analysis.RankOneFeasibility.singletonScan_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:52:25.995052+00:00
-- url     : https://prove2.me/theorems/cc323c2e-e879-4f42-a614-a88bbf0f27d9
-- title:
--   Correctness of the common-independent-singleton scan
-- statement:
--   Let $M_1,M_2$ be matroids on the ambient type $[n]$, and let $o_1,o_2$ be exact independence oracles for them. The singleton scan queries both oracles on every singleton and accumulates the disjunction of their joint answers. It returns true exactly when $$\exists I\subseteq[n],\qquad |I|=1,\quad I\text{ independent in }M_1,\quad I\text{ independent in }M_2.$$ Equivalently, its Boolean output is the decision value of this proposition.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankOneFeasibility.lean#L55-L89

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
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

namespace Arlib
end Arlib
set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility
end CountingMatroid.Analysis.RankOneFeasibility
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

theorem CountingMatroid.Analysis.RankOneFeasibility.singletonScan_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) :
    (singletonScan o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = 1 ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by sorry
