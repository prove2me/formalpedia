-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryReturnOccupation_stationary_return_occupation
-- name    : CountingMatroid.Analysis.StationaryReturnOccupation.stationary_return_occupation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:20:59.411302+00:00
-- url     : https://prove2.me/theorems/4ee4415d-9f70-4a75-9cfd-c00e9a88ec56
-- title:
--   Stationary return occupations telescope to a survival deficit
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix, $A\subseteq\Omega$, and $\mu$ a stationary probability distribution. Let $s_k(x)$ be the probability of avoiding $A$ at times $0,\ldots,k$ when started at $x$, with $s_0=\mathbf1_{\Omega\setminus A}$. For $H\in\mathbb N$, define
--   $$O_H=\mu(A)+\sum_{k=0}^{H-1}\sum_{x\in A}\mu(x)\sum_zP(x,z)s_k(z),\qquad\mu(A)=\sum_{x\in A}\mu(x).$$
--   The initial term counts the first attempted transition in a positive-time return; the following terms are survival tails.
--   Then
--   $$O_H=1-\sum_x\mu(x)s_H(x).$$
--   This exact finite-horizon identity gives an occupation budget without passing to an infinite expected return time.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryReturnOccupation.lean#L28-L52

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
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
Finite occupation bounds for positive-time returns. The first attempted step
is counted separately from the subsequent survival tails. Stationarity makes
the tails telescope, so neither irreducibility nor an infinite-expectation
interchange is needed. Operational finite-tape coupling is not asserted here.
-/
namespace CountingMatroid.Analysis.StationaryReturnOccupation
end CountingMatroid.Analysis.StationaryReturnOccupation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryReturnOccupation

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.StationaryReturnOccupation.stationary_return_occupation (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (H : ℕ) :
    returnOccupation P A μ H = 1 - ∑ x, μ x * survive P A H x := by sorry
