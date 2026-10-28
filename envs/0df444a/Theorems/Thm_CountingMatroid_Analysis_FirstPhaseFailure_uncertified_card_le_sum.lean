-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FirstPhaseFailure_uncertified_card_le_sum
-- name    : CountingMatroid.Analysis.FirstPhaseFailure.uncertified_card_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:44:11.460003+00:00
-- url     : https://prove2.me/theorems/18f13445-0dbd-49f0-b08a-19e0efbeb1f4
-- title:
--   Uncertified finite tapes are covered by first phase failures
-- statement:
--   Fix natural $n,r$, Boolean subset-oracle functions $o_1,o_2$ on $[n]=\{0,\ldots,n-1\}$, and an annealing schedule $s$ with phase count $L$, cooling parameter $\rho$, and tolerance $\eta$. Let $C_j$ be the operational transversal partition sum at $\rho^j$ and $D_{j,\alpha}$ the operational partition sum of ordered defect type $\alpha$ at that parameter. A cursor is good at level $j$ when every stored level $a\le j$ has multipliers between $(C_a/D_{a,\alpha})/4$ and $4C_a/D_{a,\alpha}$, and its current multipliers satisfy those bounds at $j$. A phase certificate $\mathcal C_j(\omega)$ requires that the actual $j$-phase prefix and next phase both succeed, the product is multiplied by a rational $R$, the input cursor is good at $j$, and the output is good at $j+1$ if $j+1<L$, with
--   $$\frac{1-\eta}{1+\eta}\le\frac{R}{C_{j+1}/C_j}\le\frac{1+\eta}{1-\eta}.$$
--   Write $\mathcal F_j(\omega)=(\forall a<j,\mathcal C_a(\omega))\land\neg\mathcal C_j(\omega)$ for first failure. All quotients use the formalization's total rational division. For every $m\in\mathbb N$, interpret a length-$m$ Boolean string $b$ as a tape $\widehat b$ extended by zeros. Then
--
--   $$\#\{b\in\{0,1\}^m:\neg\forall j<L,\mathcal C_j(\widehat b)\}
--   \le\sum_{j=0}^{L-1}\#\{b\in\{0,1\}^m:\mathcal F_j(\widehat b)\}.$$
--
--   This is a deterministic counting bound, with no independence assumption or per-phase probability estimate.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FirstPhaseFailure.lean#L80-L123

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

/-!
A local failure event for the actual charged phase prefixes. A certificate
requires completion, an accurate ratio, and good stored multipliers. First
failure events partition failure of these certificates, including aborts.
The per-phase finite-tape probability estimate remains in the consuming theorem;
it requires the paper's conditional restart and observation analysis and the
adaptive finite-tape coupling. No independence of adjacent phase events is
assumed by this representation.
-/

namespace CountingMatroid.Analysis.FirstPhaseFailure
end CountingMatroid.Analysis.FirstPhaseFailure
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FirstPhaseFailure

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

theorem CountingMatroid.Analysis.FirstPhaseFailure.uncertified_card_le_sum (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m ∧
      ¬ ∀ j < s.L, CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j} ≤
    ∑ j ∈ Finset.range s.L,
      Set.ncard {bits : List Bool | bits.length = m ∧
        FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s j} := by sorry
