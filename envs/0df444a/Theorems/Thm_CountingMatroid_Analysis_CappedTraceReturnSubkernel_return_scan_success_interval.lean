-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CappedTraceReturnSubkernel_return_scan_success_interval
-- name    : CountingMatroid.Analysis.CappedTraceReturnSubkernel.return_scan_success_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:57:10.72075+00:00
-- url     : https://prove2.me/theorems/169ec31e-3db9-47a6-a35d-8685a5c92de9
-- title:
--   Successful capped return scans replay their consumed interval
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be fixed Boolean oracle functions, let $q\in\mathbb Q$, and let $w$ assign a rational multiplier to every ordered pair of distinct indices in $[n]=\{0,\ldots,n-1\}$. Paired states are subsets of $[n]\times\{0,1\}$. A state is classifier-valid when it is either a transversal (one element from every pair) or has exactly one empty pair and one distinct full pair, with one element from every other pair. Let $s$ be an annealing schedule; write $T=s.\mathrm{drawTrials}$ for its rejection-trial cap and $R=s.\mathrm{restartCap}$ for its shared attempt cap. A restart cursor $c$ records a paired state $c.x$, a tape position $c.b$, and a count $c.a$ of attempts already used.
--
--   Fix $k\in\mathbb N$ and a restart cursor $c$. Let $S_k(\omega,c)$ be the recursive return scan on a Boolean tape $\omega:\mathbb N\to\{0,1\}$: it performs at most $k$ chain attempts, refuses attempts once the shared counter reaches $R$, and returns at the first transversal reached after an attempt. If it succeeds with cursor $d$, then
--
--   $$c.b\le d.b,\qquad \omega'|_{[c.b,d.b)}=\omega|_{[c.b,d.b)}\ \Longrightarrow\ S_k(\omega',c)=d.$$
--
--   This locality statement makes a successful stopped scan depend only on the tape segment it consumed.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CappedTraceReturnSubkernel.lean#L30-L57

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The successful finite-tape sublaw of an operational positive-time return.
The recursive scan keeps the global attempt counter and aborts explicitly. -/
namespace CountingMatroid.Analysis.CappedTraceReturnSubkernel
end CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedTraceReturnSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel

theorem CountingMatroid.Analysis.CappedTraceReturnSubkernel.return_scan_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (w : Multipliers n) (k : ℕ) (current : RestartCursor n) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => returnScan r o₁ o₂ tape s q w k current)
      RestartCursor.bitCursor current.bitCursor := by sorry
