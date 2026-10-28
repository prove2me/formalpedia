-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceKernel_endpoint_mass_le_of_capped_trace
-- name    : CountingMatroid.Analysis.PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:10:40.766677+00:00
-- url     : https://prove2.me/theorems/56f28cbd-c26f-4d54-9fbe-60c8d3020af2
-- title:
--   Endpoint bound from capped-to-uncapped trace comparison
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix on $\Omega$, and $A\subseteq\Omega$. Let $R_A(x,y)$ be the uncapped positive-time return kernel: the probability that the first visit to $A$ after at least one transition ends at $y$. Its entries are the increasing limits of finite-horizon return probabilities, retaining any missing mass. Let $R_A^k$ denote ordinary kernel composition, with $R_A^0$ the identity.
--
--   Let $c,k\in\mathbb N$ be a per-return horizon and a number of trace transitions. Write $R_{A,c}$ for the kernel counting only positive-time returns completed within $c$ transitions, with aborted mass retained as missing mass. Let $\nu:\Omega\to\mathbb R$ satisfy $\nu(x)\ge0$, $\sum_x\nu(x)\le1$, and $\nu(x)=0$ for $x\notin A$. Fix $y\in\Omega$, real numbers $e,b$, and suppose
--   $$b\ge0,\qquad e\le\sum_x\nu(x)R_{A,c}^{\,k}(x,y),\qquad R_A^k(x,y)\le b\quad(x\in A).$$
--   Then
--   $$e\le b.$$
--   This transfers a uniform uncapped endpoint estimate to any operational endpoint mass dominated by the capped trace mixture.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceKernel.lean#L245-L271

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
set_option autoImplicit false

/-!
Finite positive-time return kernels. Each row counts only returns completed
within the horizon; missing mass is retained as abort mass. The construction
uses the library's zero-time hitting recursion only after an initial transition,
so a starting transversal is not mistaken for an immediate return. Stationarity
also proves almost-sure return from positive-mass target states. This module
does not claim the spectral estimate or finite-bit operational coupling.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceKernel
end CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceKernel

open Arlib.Probability Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace (P : FinChain Ω) (A : Finset Ω)
    (cap steps : ℕ) (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hνmass : ∑ x, ν x ≤ 1) (hνsupport : ∀ x, x ∉ A → ν x = 0)
    (endpointMass bound : ℝ) (hbound : 0 ≤ bound) (y : Ω)
    (hoperational : endpointMass ≤
      ∑ x, ν x * (iterate (returnWithin P A cap) steps).entry x y)
    (hmixing : ∀ x ∈ A,
      (iterate (uncappedReturn P A) steps).entry x y ≤ bound) :
    endpointMass ≤ bound := by sorry
