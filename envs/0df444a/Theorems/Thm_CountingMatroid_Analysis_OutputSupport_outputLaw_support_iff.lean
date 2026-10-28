-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_OutputSupport_outputLaw_support_iff
-- name    : CountingMatroid.Analysis.OutputSupport.outputLaw_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:57:35.697116+00:00
-- url     : https://prove2.me/theorems/7fb443f5-6458-4890-8cbc-e36a08f5318b
-- title:
--   Support of the reported output law
-- statement:
--   Fix natural numbers $n,r$, Boolean query functions $o_1,o_2$ on subsets of $[n]$, a candidate feasibility implementation that returns a charged Boolean computation for each input, and parameters $p=(\varepsilon,\delta)$ with rational $0<\varepsilon,\delta<1$. Let $\mu$ be the algorithm law of charged rational-valued runs, obtained by executing the estimator on its sampled finite fair-bit blocks. For a run $a$, let $O(a)$ count calls to the two original oracles, $W(a)$ count fair-bit reads plus the charged named nonoracle instructions, and $B(a)$ count fair-bit reads. Let $\nu$ be the output law, reporting the rational value and cost triple. For any rational value and natural cost triple $x$, $$x\in\operatorname{supp}(\nu)\ \Longleftrightarrow\ \exists a\in\operatorname{supp}(\mu),\quad(a.\mathrm{value},(O(a),W(a),B(a)))=x.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/OutputSupport.lean#L29-L53

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

namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OutputSupport

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

theorem CountingMatroid.Analysis.OutputSupport.outputLaw_support_iff (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (x : ℚ × ExecutionCost) :
    x ∈ (Model.Run.outputLaw solver n r o₁ o₂ p).support ↔
      ∃ run ∈ (Model.Run.algorithmLaw solver n r o₁ o₂ p).support,
        (run.val,
          { oracleCalls := oracleCalls run,
            bitOps := otherSteps run,
            randomBits := run.cost Operations.Op.fairBit }) = x := by sorry
