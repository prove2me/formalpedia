-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_abort_mass
-- name    : CountingMatroid.Analysis.BoundedUniformAbortMass.boundedUniform_abort_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:27:22.970552+00:00
-- url     : https://prove2.me/theorems/c570cdf5-9aa6-459a-879c-714ce4c0530b
-- title:
--   Finite-suffix probability of exhausting a rejection cap
-- statement:
--   For a finite Boolean prefix $h$ and $t\in\mathbb N$, write $\mathbb P_{h,t}(E)$ for the fraction of the $2^t$ Boolean suffixes $b$ of length $t$ for which $E$ holds on the tape $h\mathbin{+\!+}b$, extended by zeros beyond its end.
--
--   Write $D_{T,v,c}(\omega)$ for the value and final cursor of the bounded integer sampler on Boolean tape $\omega$, with at most $T$ trials, range $\{0,\ldots,v-1\}$, and initial cursor $c$. A successful result is denoted $(a,s)$ and failure has value $\bot$.
--
--   Put $w=\operatorname{log}_2(v\mathbin{\dot-}1)+1$, where $\dot-$ is truncated natural subtraction and the natural-number base-two logarithm convention is $\operatorname{log}_2(0)=0$. For every prefix $h$ and natural $T,v,t$ with $v>0$ and $Tw\le t$,
--
--   $$\mathbb P_{h,t}\bigl(D_{T,v,|h|}(\omega).\mathrm{value}=\bot\bigr)\le2^{-T}.$$
--
--   This controls a fixed positive denominator and fully covered trial budget, including zero trials. The formal statement expresses the probability as a rational counting ratio.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedUniformAbortMass.lean#L251-L289

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

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass
end CountingMatroid.Analysis.BoundedUniformAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

theorem CountingMatroid.Analysis.BoundedUniformAbortMass.boundedUniform_abort_mass (pref : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} : ℚ) / (2 : ℚ) ^ t ≤
      (1 / 2 : ℚ) ^ trials := by sorry
