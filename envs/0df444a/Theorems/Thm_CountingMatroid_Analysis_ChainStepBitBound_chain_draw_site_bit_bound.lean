-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_draw_site_bit_bound
-- name    : CountingMatroid.Analysis.ChainStepBitBound.chain_draw_site_bit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:39:48.873755+00:00
-- url     : https://prove2.me/theorems/518cdb76-a647-443b-b773-589b4295e79b
-- title:
--   A reached draw and all its trials fit the chain tape budget
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be fixed Boolean oracle functions, let $q\in\mathbb Q$, and let $w$ assign a rational multiplier to every ordered pair of distinct indices in $[n]=\{0,\ldots,n-1\}$. Paired states are subsets of $[n]\times\{0,1\}$. A state is classifier-valid when it is either a transversal (one element from every pair) or has exactly one empty pair and one distinct full pair, with one element from every other pair. Let $s$ be an annealing schedule; write $T=s.\mathrm{drawTrials}$ for its rejection-trial cap and $R=s.\mathrm{restartCap}$ for its shared attempt cap. A restart cursor $c$ records a paired state $c.x$, a tape position $c.b$, and a count $c.a$ of attempts already used. For a rational $a$, write $\operatorname{len}(a)=2+(\operatorname{log2}|\operatorname{num}(a)|+1)+(\operatorname{log2}\operatorname{den}(a)+1)$, using its canonical numerator and positive denominator and $\operatorname{log2}(0)=0$. Let $K\in\mathbb N$ satisfy
--
--   $$\operatorname{len}(1)+n\operatorname{len}(q)\le K,\qquad \operatorname{len}(w_{ij})\le K\quad(i\ne j).$$
--
--   Fix a tape $\omega:\mathbb N\to\{0,1\}$, a paired state $X$, and a starting cursor $c\in\mathbb N$. If site $j\in\{0,1,2\}$ reports descriptor $(b,v)$, then, with $\ell(v)=\operatorname{log2}(v\mathbin{\dot-}1)+1$,
--
--   $$b+T\ell(v)\le c+1+3T(4K+n+1).$$
--
--   Here $b$ is the cursor before the reported draw and $v$ is its range. Thus its entire allotted rejection-trial budget fits the same bound, even if that draw later aborts.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepBitBound.lean#L160-L218

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

theorem CountingMatroid.Analysis.ChainStepBitBound.chain_draw_site_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (site : Fin 3) (d : ℕ × ℕ)
    (h : chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by sorry
