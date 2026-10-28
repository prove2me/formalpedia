-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CertifiedPhaseRatioSteps_certified_phases_ratio_steps
-- name    : CountingMatroid.Analysis.CertifiedPhaseRatioSteps.certified_phases_ratio_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:45:26.277623+00:00
-- url     : https://prove2.me/theorems/cd1c18ca-e746-4244-a720-7d5b40e13b25
-- title:
--   Certified phases yield positive operational ratio steps
-- statement:
--   Let $n,r\in\mathbb N$ with $n>0$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be Boolean oracle functions, and let the rational accuracy and failure parameters $\varepsilon,\delta$ satisfy $0<\varepsilon,\delta<1$. Let $s$ be the program's schedule computed from these inputs, with phase count $L$, cooling factor $\rho$, and phase tolerance $\eta$. Fix a Boolean tape $\omega$. Write $C_j=\sum_{A\subseteq[n]}(\rho^j)^{d(A)}$, where $d(A)$ is the natural-number deficiency computed by the paired-rank routine on the transversal encoded by $A$.
--
--   Assume every phase $j<L$ has a certificate: the actually reached cursor and its next cursor exist, their stored products satisfy $p_{j+1}=p_j a_j$ for a ratio $a_j$ with the prescribed relative bounds, and its stored tables at all levels $a\le j$ and its current multipliers at level $j$ lie between one quarter and four times their respective ideal partition-sum ratios. When $j+1<L$, require the corresponding table and current-multiplier bounds at the next cursor through level $j+1$. Then every such phase is an operational ratio step: its actual transition succeeds, its two products are positive, and
--
--   $$0<p_j,\quad 0<p_{j+1},\qquad \frac{1-\eta}{1+\eta}\le\frac{p_{j+1}/p_j}{C_{j+1}/C_j}\le\frac{1+\eta}{1-\eta}.$$
--
--   The ideal multiplier for an ordered defect is the transversal partition sum divided by that defect class's unmultiplied partition sum at the corresponding cooling level. This result extracts the product-ratio invariant from the stronger certificates.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CertifiedPhaseRatioSteps.lean#L12-L91

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
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps
end CountingMatroid.Analysis.CertifiedPhaseRatioSteps
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps
end CountingMatroid.Analysis.CertifiedPhaseRatioSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CertifiedPhaseRatioSteps

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.BoundedRunPhaseHistory

theorem CountingMatroid.Analysis.CertifiedPhaseRatioSteps.certified_phases_ratio_steps {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (tape : ℕ → Bool)
    (hcert : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
        (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j := by sorry
