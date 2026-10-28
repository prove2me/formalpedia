-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_MedianAmplification_independent_runs_majority_tail
-- name    : CountingMatroid.Analysis.MedianAmplification.independent_runs_majority_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:58:54.485032+00:00
-- url     : https://prove2.me/theorems/a8bc3931-12a1-43b8-8864-c3df8cd35384
-- title:
--   Exponential majority bound for independent repeated runs
-- statement:
--   Let $\mu$ be a probability mass function on $\mathbb Q$ and let $\mathrm{bad}:\mathbb Q\to\{0,1\}$ mark bad outputs. Suppose a single draw is bad with probability at most $1/4$. For $b\in\mathbb N$, take $m=10b+1$ independent draws from $\mu$, and let $N_{\mathrm{bad}}$ count bad outputs. Then
--
--   $$\Pr\!\left(N_{\mathrm{bad}}\ge\left\lfloor\frac m2\right\rfloor+1\right)
--   =\Pr(N_{\mathrm{bad}}\ge5b+1)\le2^{-b}.$$
--
--   The formal probabilities are the outer measures induced by the discrete probability mass functions. This supplies the tail estimate used in median amplification.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IndependentRunsTail.lean#L93-L160

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_IndependentRunsCore
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification
end CountingMatroid.Analysis.MedianAmplification
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.MedianAmplification

theorem CountingMatroid.Analysis.MedianAmplification.independent_runs_majority_tail (q : PMF ℚ) (bad : ℚ → Bool) (b : ℕ)
    (hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal)) :
    (independentRuns q (10 * b + 1)).toOuterMeasure
      {xs | (10 * b + 1) / 2 + 1 ≤ xs.countP bad} ≤
      (1 / 2 : ENNReal) ^ b := by sorry
