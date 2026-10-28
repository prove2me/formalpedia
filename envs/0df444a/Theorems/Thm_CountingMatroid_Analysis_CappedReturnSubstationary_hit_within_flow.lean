-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_hit_within_flow
-- name    : CountingMatroid.Analysis.CappedReturnSubstationary.hit_within_flow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:19:30.501506+00:00
-- url     : https://prove2.me/theorems/9b499be8-d4ff-4c19-9548-a55d57ef071f
-- title:
--   Finite hitting mass decomposes into killed arrival flows
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, let $P$ be a Markov transition matrix, let $A\subseteq\Omega$, let $k\in\mathbb N$, and let $\lambda:\Omega\to\mathbb R$ be arbitrary real weights. Define killed flow by
--
--   $$f_0(x)=\lambda(x),\qquad f_{s+1}(x)=\sum_{z\notin A}f_s(z)P(z,x).$$
--
--   Let $H_k(z,x)$ be the subprobability kernel for first hitting $A$ at $x$ within $k$ transitions, counting time zero when the start lies in $A$. For every $x\in A$,
--
--   $$\sum_{z\in\Omega}\lambda(z)H_k(z,x)=\sum_{s=0}^k f_s(x).$$
--
--   This expresses hitting mass as accumulated arrivals before killed mass can leave the target. Nonnegativity, normalization, and stationarity of $\lambda$ are not required.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CappedReturnSubstationary.lean#L37-L84

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

theorem CountingMatroid.Analysis.CappedReturnSubstationary.hit_within_flow (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (lam : Ω → ℝ)
    (x : Ω) (hx : x ∈ A) :
    (∑ z, lam z * (hitWithin P A k).entry z x) =
      ∑ s ∈ Finset.range (k + 1), killedFlow P A lam s x := by sorry
