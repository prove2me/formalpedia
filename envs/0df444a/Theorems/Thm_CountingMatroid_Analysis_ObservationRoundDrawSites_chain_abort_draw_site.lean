-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ObservationRoundDrawSites_chain_abort_draw_site
-- name    : CountingMatroid.Analysis.ObservationRoundDrawSites.chain_abort_draw_site
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:29:13.691914+00:00
-- url     : https://prove2.me/theorems/2fff0ace-5a0b-46f1-8076-74b95ab22426
-- title:
--   A chain abort comes from an actual capped draw
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be fixed Boolean oracle functions, let $q\in\mathbb Q$, and let $w$ assign a rational multiplier to every ordered pair of distinct indices in $[n]=\{0,\ldots,n-1\}$. Paired states are subsets of $[n]\times\{0,1\}$. A state is classifier-valid when it is either a transversal (one element from every pair) or has exactly one empty pair and one distinct full pair, with one element from every other pair. Let $s$ be an annealing schedule; write $T=s.\mathrm{drawTrials}$ for its rejection-trial cap and $R=s.\mathrm{restartCap}$ for its shared attempt cap. A restart cursor $c$ records a paired state $c.x$, a tape position $c.b$, and a count $c.a$ of attempts already used.
--
--   Fix a tape $\omega:\mathbb N\to\{0,1\}$, a classifier-valid state $X$, and a starting cursor $c\in\mathbb N$. If the chain step aborts, there exist a draw site $j\in\{0,1,2\}$ and a descriptor $(b,v)\in\mathbb N^2$ such that
--
--   $$\operatorname{chainDrawSite}(\omega,X,c,j)=\operatorname{some}(b,v),\qquad \operatorname{boundedUniform}(\omega,T,v,b).\mathrm{value}=\operatorname{none}.$$
--
--   Sites zero and one select occupied and unoccupied indices; site two is the conditional rational acceptance draw. A descriptor records the cursor and bound immediately before that draw. No positivity or approximation condition on the multipliers is assumed.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainDrawAbortAttribution.lean#L93-L199

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
set_option autoImplicit false

/-!
Abort attribution for a chain attempt from a non-invalid state. Successful
bounded draws return in-range indices, classified states have weight values,
and the imported selection correctness invariant excludes failed lookups.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

theorem CountingMatroid.Analysis.ObservationRoundDrawSites.chain_abort_draw_site {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (habort : (chainStep r o₁ o₂ tape s.drawTrials q weights state cursor).val = none) :
    ∃ site d, chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d ∧
      (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none := by sorry
