-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunPhaseHistory_successful_history_product
-- name    : CountingMatroid.Analysis.BoundedRunPhaseHistory.successful_history_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:45:36.271994+00:00
-- url     : https://prove2.me/theorems/f7a4af6d-5b65-4857-9256-5f058e1556bf
-- title:
--   Successful local phases reconstruct the executed ratio product
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. Let $p=(\varepsilon,\delta)$ consist of rational accuracy and confidence parameters with $0<\varepsilon<1$ and $0<\delta<1$. Let $s$ be the setup schedule, with phase count $L$, cooling factor $\rho$, and local tolerance $\eta$. Let $H_j$ be the actual optional cursor after $j$ phases, initialized with product $1$, multipliers $4$, allocated tables, and tape position zero. Write $P_j$ for its product when present. Let $$C_j=\sum_{A\subseteq[n]}(\rho^j)^{d(A)},$$ where $d(A)=\max(n-R(X_A),0)$, $R$ is the paired-rank scan with $r,o_1,o_2$, and $X_A$ chooses the first copy on $A$ and the second copy on its complement. Call phase $j$ good when $H_j$ is present, its actual phase transition succeeds with positive input and output products, and $$\frac{1-\eta}{1+\eta}\le\frac{P_{j+1}/P_j}{C_{j+1}/C_j}\le\frac{1+\eta}{1-\eta}.$$ If every phase $j<L$ is good, then there is a rational sequence $(R_j)_{j\ge0}$ and a present final cursor such that $$P_L=\prod_{j=0}^{L-1}R_j,$$ and, for every $j<L$, $$\frac{1-\eta}{1+\eta}\le\frac{R_j}{C_{j+1}/C_j}\le\frac{1+\eta}{1-\eta}.$$ This recovers an accurate-ratio witness from the actual execution rather than assuming a separate transcript.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhaseHistory.lean#L101-L167

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
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory
end CountingMatroid.Analysis.BoundedRunPhaseHistory
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

theorem CountingMatroid.Analysis.BoundedRunPhaseHistory.successful_history_product {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (hgood : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
    ∃ R : ℕ → ℚ,
      (∃ current : AnnealingCursor n,
        phaseHistory r o₁ o₂ tape s s.L = some current ∧
        current.product = ∏ j ∈ Finset.range s.L, R j) ∧
      ∀ j < s.L,
        (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
        R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η) := by sorry
