-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_weightOfKind_work_size
-- name    : CountingMatroid.Analysis.PhaseChainWork.weightOfKind_work_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:29:34.928096+00:00
-- url     : https://prove2.me/theorems/b853c69d-35e6-4574-abbf-966f1d5369bc
-- title:
--   Work and output length of a state-weight computation
-- statement:
--   Let $n,r\in\mathbb N$, and let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]=\{0,\ldots,n-1\}$. For a reduced rational $a=u/v$ with $v>0$, put $\ell(a)=2+(\log_2|u|+1)+(\log_2v+1)$, using floor natural logarithms and $\log_2 0=0$.
--
--   Let $q\in\mathbb Q$, let $w$ assign a rational multiplier to each ordered pair $(i,k)$ with $i\ne k$ in $[n]$, let $S\subseteq[n]\times\{0,1\}$, let $a$ be any state-kind label (transversal, defect, or invalid), and let $K\in\mathbb N$. Assume
--   $$\ell(1)+n\ell(q)\le K,\qquad \ell(w_{ik})\le K\ (i\ne k).$$
--   Write $F=\operatorname{weightOfKind}(r,o_1,o_2,q,w,S,a)$. It computes $q^d$ for transversal kind, $w_{ik}q^d$ for a distinct-index defect, and fails on invalid or diagonal-defect kinds, where $d=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ is truncated natural subtraction and paired rank is the program’s oracle-based scan. Here $W$ is the model’s `otherSteps` counter, summing fair-bit and nonoracle word-operation charges.
--   $$W(F)\le8(n+1)^3+(n+4)K^2+n^2+2,\qquad F=\operatorname{some}(z)\Longrightarrow\ell(z)\le2K.$$
--   The paired bounds supply both work and operand size for the acceptance calculation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseChainWork.lean#L201-L262

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
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
end CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

theorem CountingMatroid.Analysis.PhaseChainWork.weightOfKind_work_size {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) (kind : StateKind n)
    (K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (weightOfKind r o₁ o₂ q weights state kind) ≤
      8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2 ∧
    (∀ w, (weightOfKind r o₁ o₂ q weights state kind).val = some w →
      binaryRatLength w ≤ 2 * K) := by sorry
