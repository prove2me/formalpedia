-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceHarmonic_uncappedReturn_reversible
-- name    : CountingMatroid.Analysis.PositiveTimeTraceHarmonic.uncappedReturn_reversible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:36:15.889166+00:00
-- url     : https://prove2.me/theorems/587d8c6b-1936-43c6-8311-840b254ba842
-- title:
--   Detailed balance for the uncapped positive-time return kernel
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix on $\Omega$, and $A\subseteq\Omega$. Let $R_A(x,y)$ be the uncapped positive-time return kernel: the probability that the first visit to $A$ after at least one transition ends at $y$. Its entries are the increasing limits of finite-horizon return probabilities, retaining any missing mass. Let $R_A^k$ denote ordinary kernel composition, with $R_A^0$ the identity.
--
--   Let $\mu$ be a probability distribution reversible for $P$, meaning $\mu(x)P(x,y)=\mu(y)P(y,x)$ for every $x,y\in\Omega$. Then for all $x,y\in A$,
--   $$\mu(x)R_A(x,y)=\mu(y)R_A(y,x).$$
--   This gives detailed balance on the return boundary, including states of zero stationary mass.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceHarmonic.lean#L132-L156

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic
end CountingMatroid.Analysis.PositiveTimeTraceHarmonic
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.PositiveTimeTraceHarmonic.uncappedReturn_reversible (μ : FinDist Ω) (P : FinChain Ω)
    (hrev : Reversible μ P) (A : Finset Ω) (x y : Ω)
    (hx : x ∈ A) (hy : y ∈ A) :
    μ x * (uncappedReturn P A).entry x y =
      μ y * (uncappedReturn P A).entry y x := by sorry
