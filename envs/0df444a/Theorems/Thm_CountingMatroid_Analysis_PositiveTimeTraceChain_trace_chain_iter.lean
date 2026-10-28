-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceChain_trace_chain_iter
-- name    : CountingMatroid.Analysis.PositiveTimeTraceChain.trace_chain_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:04:41.590265+00:00
-- url     : https://prove2.me/theorems/5ad25fe7-ef6f-4ad2-9567-c19ca5029564
-- title:
--   Finite powers of the trace chain agree with return-kernel powers
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix on $\Omega$, and $A\subseteq\Omega$. Let $R_A(x,y)$ be the uncapped positive-time return kernel: the probability that the first visit to $A$ after at least one transition ends at $y$. Its entries are the increasing limits of finite-horizon return probabilities, retaining any missing mass. Let $R_A^k$ denote ordinary kernel composition, with $R_A^0$ the identity.
--
--   Let $\mu$ be a probability distribution stationary for $P$, and assume $\mu(x)>0$ for every $x\in A$. Almost-sure return then makes $T_A(x,y)=R_A(x,y)$ a stochastic chain on the state space $A$. For every $k\in\mathbb N$ and $x,y\in A$,
--   $$T_A^k(x,y)=R_A^k(x,y).$$
--   The right side is composed on all of $\Omega$, while the left side is composed on $A$. This identifies the two finite-transition descriptions of the trace.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceChain.lean#L73-L93

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib
end Arlib
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
set_option autoImplicit false

/-!
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain
end CountingMatroid.Analysis.PositiveTimeTraceChain
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.PositiveTimeTraceChain.trace_chain_iter (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω) (hμ : ∀ x ∈ A, 0 < μ x)
    (k : ℕ) (x y : A) :
    (traceChain μ P hst A hμ).iter k x y =
      (iterate (uncappedReturn P A) k).entry x y := by sorry
