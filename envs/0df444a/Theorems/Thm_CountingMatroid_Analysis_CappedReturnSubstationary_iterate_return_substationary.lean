-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_iterate_return_substationary
-- name    : CountingMatroid.Analysis.CappedReturnSubstationary.iterate_return_substationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:02:25.200345+00:00
-- url     : https://prove2.me/theorems/fb2257a9-090d-46a6-8b31-650d12545170
-- title:
--   Stationary domination survives iterated capped returns
-- statement:
--   Let $P$ be a Markov transition matrix on a finite space $\Omega$, let $A\subseteq\Omega$, and let $\mu$ be a stationary probability distribution. Let $K_k$ be the first positive-time return subkernel to $A$ capped at $k\in\mathbb N$, and put $\mu_A=\mathbf1_A\mu$. Given $c\in\mathbb R$ with $c\ge0$ and a function $\lambda:\Omega\to\mathbb R$ satisfying $0\le\lambda(y)\le c\mu_A(y)$ for every $y$, one has, for every $m\in\mathbb N$ and $x\in\Omega$,
--
--   $$\sum_y\lambda(y)K_k^m(y,x)\le c\mu_A(x),\qquad K_k^0=I.$$
--
--   The initial function need not be normalized. The bound retains the missing mass of each capped return.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CappedReturnSubstationary.lean#L149-L187

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

theorem CountingMatroid.Analysis.CappedReturnSubstationary.iterate_return_substationary (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (lam : Ω → ℝ) (hlam0 : ∀ y, 0 ≤ lam y)
    (hlam : ∀ y, lam y ≤ c * (if y ∈ A then μ y else 0)) (steps : ℕ) (x : Ω) :
    (∑ y, lam y * (iterate (returnWithin P A k) steps).entry y x) ≤
      c * (if x ∈ A then μ x else 0) := by sorry
