-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_EmpiricalPhaseCertificate_raw_phase_certified
-- name    : CountingMatroid.Analysis.EmpiricalPhaseCertificate.raw_phase_certified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:16:32.627518+00:00
-- url     : https://prove2.me/theorems/dd34dadf-5db4-4154-9d00-aefeecfc7c5d
-- title:
--   Raw empirical phase estimates imply the operational phase certificate
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be Boolean subset oracles on an $n$-element set. Fix a tape $t:\mathbb N\to\{0,1\}$, an annealing schedule $s$, and a phase index $j\in\mathbb N$, with $0\le\eta=s.\eta\le1/3$. Index defect classes by ordered distinct pairs $\alpha=(e,f)$, with pair $e$ empty and pair $f$ full. All other pairs are singly occupied. For a paired state $S$, let $\mathsf r(S)$ be its operational paired-rank value; the unmultiplied weight at parameter $q_a$ is $q_a^{\max(n-\mathsf r(S),0)}$. Let $C_a$ be the transversal partition sum at $q_a=s.\rho^a$, let $D_a(\alpha)$ be the corresponding unmultiplied defect partition sum, and set $$I_a(\alpha)=C_a/D_a(\alpha),\qquad R_j=C_{j+1}/C_j.$$ Assume the actual phase history reaches a cursor $c$, its restart succeeds at a state/tape pair, and its observation phase succeeds with counts $c_0,c_\alpha$ and numerator $U$. Assume $c$ has factor-four good multipliers: current weights approximate $I_j$, and stored tables at each level $a\le j$ approximate $I_a$, between one quarter and four times those values.
--
--   Suppose also that $N=s.\mathrm{observations}>0$ and there exist $p_0>0,p_\alpha>0$ with $R_j>0$, positive current multipliers $w_\alpha$, $$I_j(\alpha)=w_\alpha p_0/p_\alpha,\qquad I_j(\alpha)/2\le I_{j+1}(\alpha)\le2I_j(\alpha),$$ and relative error at most $\eta$ for $c_0/N$, $U/N$, and $c_\alpha/N$ against $p_0$, $p_0R_j$, and $p_\alpha$, respectively. Then phase $j$ is certified: its actual transition reaches a cursor $c'$ and a ratio $\widehat R$ with $$c'.\mathrm{product}=c.\mathrm{product}\,\widehat R,\qquad\frac{1-\eta}{1+\eta}\le\frac{\widehat R}{R_j}\le\frac{1+\eta}{1-\eta},$$ retaining the input good-multiplier guarantees and establishing them at level $j+1$ whenever $j+1<s.L$. This connects raw observations to the exact executed update.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EmpiricalPhaseCertificate.lean#L123-L161

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
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.EmpiricalPhaseCertificate
end CountingMatroid.Analysis.EmpiricalPhaseCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.EmpiricalPhaseCertificate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

theorem CountingMatroid.Analysis.EmpiricalPhaseCertificate.raw_phase_certified {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hraw : RawPhaseEstimates r o₁ o₂ tape s j) :
    FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j := by sorry
