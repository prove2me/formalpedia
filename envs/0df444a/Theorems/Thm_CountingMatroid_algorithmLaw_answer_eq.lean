-- Prove2me | Theorems.Thm_CountingMatroid_algorithmLaw_answer_eq
-- name    : CountingMatroid.algorithmLaw_answer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:09:36.993424+00:00
-- url     : https://prove2.me/theorems/41a46539-6d19-4730-8595-604b892afb96
-- title:
--   The charged algorithm law projects to the pseudocode answer law
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, $E=I\times\{0,1\}$, and $\Omega=\mathcal P(E)$. Let $o_1,o_2$ be Boolean oracles on subsets of $I$. Write $R(S)$ for the natural-number value of the paired-rank routine with parameter $r$ and these oracles, and $d(S)=n-R(S)$ with subtraction truncated at zero. Let $p=(\varepsilon,\delta)$ consist of rational parameters $0<\varepsilon,\delta<1$. Write $s=\operatorname{setup}(n,p)$ for the prescribed annealing schedule, $L=s.L$ for its phase count, $\rho=s.\rho$ for its temperature ratio, $\eta=s.\eta$ for its relative mean tolerance, and $N=s.\mathrm{observations}$ for its sample count. Let $F$ be any feasibility implementation. Let $\mathcal A_F$ be the law of charged estimator runs on the scheduled independent fair finite blocks, let $\mathcal P_F$ be the law of the pseudocode estimate on the same blocks, and let $\operatorname{val}$ discard the charged counters. Then $$\operatorname{val}_*\mathcal A_F=\mathcal P_F.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Interface/ProgramModel.lean#L94-L112

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

namespace CountingMatroid
end CountingMatroid
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid
end CountingMatroid
open CountingMatroid

theorem CountingMatroid.algorithmLaw_answer_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Model.Run.algorithmLaw solver n r o₁ o₂ p).map Arlib.Computation.Charged.val = CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p := by sorry
