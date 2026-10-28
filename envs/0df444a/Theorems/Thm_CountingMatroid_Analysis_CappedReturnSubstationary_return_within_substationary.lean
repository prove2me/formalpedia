-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_return_within_substationary
-- name    : CountingMatroid.Analysis.CappedReturnSubstationary.return_within_substationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:41:03.452163+00:00
-- url     : https://prove2.me/theorems/c083f5cb-719e-41d3-a6f8-c2f64e3c9141
-- title:
--   Capped positive-time returns are substationary
-- statement:
--   Let $P$ be a Markov transition matrix on a finite state space $\Omega$, let $A\subseteq\Omega$, and let $\mu$ be a stationary probability distribution. Write $\mu_A(x)=\mathbf1_A(x)\mu(x)$ and let $K_k(y,x)$ be the probability mass of the first positive-time visit to $A$ occurring within $k$ transitions and ending at $x$. Set $K_0=0$. For every $k\in\mathbb N$ and $x\in\Omega$,
--
--   $$\sum_{y\in\Omega}\mu_A(y)K_k(y,x)\le\mu_A(x).$$
--
--   The restricted stationary law dominates its image under a capped return; mass lost at the cap is not renormalized.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CappedReturnSubstationary.lean#L126-L147

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_CappedReturnSubstationary
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
Capped positive-time returns started from the stationary law restricted to
the target never put more mass on a target state than the stationary law
does. Iterating, any start dominated by a multiple of the restricted
stationary law stays dominated through every number of capped returns.
Lost (capped) mass is retained as a deficit, not renormalised.
-/
namespace CountingMatroid.Analysis.CappedReturnSubstationary
end CountingMatroid.Analysis.CappedReturnSubstationary
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedReturnSubstationary

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.CappedReturnSubstationary.return_within_substationary (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (x : Ω) :
    (∑ y, (if y ∈ A then μ y else 0) * (returnWithin P A k).entry y x) ≤
      if x ∈ A then μ x else 0 := by sorry
