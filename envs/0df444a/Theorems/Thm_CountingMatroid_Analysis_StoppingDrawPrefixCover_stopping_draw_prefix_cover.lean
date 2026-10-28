-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StoppingDrawPrefixCover_stopping_draw_prefix_cover
-- name    : CountingMatroid.Analysis.StoppingDrawPrefixCover.stopping_draw_prefix_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:15:51.146662+00:00
-- url     : https://prove2.me/theorems/e238c9f6-8417-4dd0-bb95-e2a513cfbcbf
-- title:
--   Local stopping descriptors admit a covered prefix-free cover
-- statement:
--   Let $T,t\in\mathbb N$ and let a partial stopping function on Boolean lists return a pair $(c,v)\in\mathbb N^2$. For each length-$t$ list $x$ on which it returns $(c,v)$, assume
--   $$v>0,\qquad c+T\bigl(\log_2(v-1)+1\bigr)\le t,$$
--   and assume every other length-$t$ list extending $\operatorname{take}_c(x)$ has that same stopping result. The logarithm uses $\log_2 0=0$. Then there exist a finite prefix-free family $\mathcal H$ and denominators $d(h)>0$ with
--   $$|h|+T\bigl(\log_2(d(h)-1)+1\bigr)\le t\quad(h\in\mathcal H),$$
--   such that every actual stopping result is represented:
--   $$|x|=t,\ \operatorname{stop}(x)=(c,v)\Longrightarrow\exists h\in\mathcal H:\ h\preceq x,\ |h|=c,\ d(h)=v.$$
--   This packages stopping locality and explicit trial coverage into the finite cover used for adaptive rejection analysis.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StoppingDrawPrefixCover.lean#L16-L84

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
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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

namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

/-!
Construct a draw cover from a deterministic stopped draw descriptor. A
descriptor records the consumed suffix length and denominator. Locality of
the stopped descriptor, positivity, and trial coverage are explicit premises;
no program reachability or quantitative bit-length assertion is assumed.
-/

namespace CountingMatroid.Analysis.StoppingDrawPrefixCover
end CountingMatroid.Analysis.StoppingDrawPrefixCover
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StoppingDrawPrefixCover

open CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

theorem CountingMatroid.Analysis.StoppingDrawPrefixCover.stopping_draw_prefix_cover (trials t : ℕ)
    (stop : List Bool → Option (ℕ × ℕ))
    (hbound : ∀ bits, bits.length = t → ∀ d, stop bits = some d →
      0 < d.2 ∧ d.1 + trials * ((d.2 - 1).log2 + 1) ≤ t)
    (hlocal : ∀ bits, bits.length = t → ∀ d, stop bits = some d →
      ∀ other, other.length = t → bits.take d.1 <+: other → stop other = some d) :
    ∃ cover : DrawPrefixCover trials t,
      ∀ bits, bits.length = t → ∀ d, stop bits = some d →
        ∃ head ∈ cover.prefixes, head <+: bits ∧
          head.length = d.1 ∧ cover.denominator head = d.2 := by sorry
