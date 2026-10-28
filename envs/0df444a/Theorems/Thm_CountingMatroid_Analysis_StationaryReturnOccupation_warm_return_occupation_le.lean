-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryReturnOccupation_warm_return_occupation_le
-- name    : CountingMatroid.Analysis.StationaryReturnOccupation.warm_return_occupation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:41:26.340307+00:00
-- url     : https://prove2.me/theorems/27d6c4ab-702f-4c41-80bc-3b69796919f1
-- title:
--   A scaled finite return-occupation bound
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix, $A\subseteq\Omega$, and $\mu$ a stationary probability distribution. Let $s_k(x)$ be the probability of avoiding $A$ at times $0,\ldots,k$ when started at $x$, with $s_0=\mathbf1_{\Omega\setminus A}$. For $H\in\mathbb N$, define
--   $$O_H=\mu(A)+\sum_{k=0}^{H-1}\sum_{x\in A}\mu(x)\sum_zP(x,z)s_k(z),\qquad\mu(A)=\sum_{x\in A}\mu(x).$$
--   The initial term counts the first attempted transition in a positive-time return; the following terms are survival tails.
--   Let $U,B\in\mathbb R$ satisfy $U\ge0$, $\mu(A)>0$, and $1\le B\mu(A)$. Then
--   $$\frac{U}{\mu(A)}O_H\le UB.$$
--   The quantity $B$ is an upper bound on the reciprocal target mass; this inequality supplies a finite occupation budget after scaling by a nonnegative warm-start factor $U$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryReturnOccupation.lean#L54-L74

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

theorem CountingMatroid.Analysis.StationaryReturnOccupation.warm_return_occupation_le (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (H : ℕ)
    (U B : ℝ) (hU : 0 ≤ U) (hmass : 0 < ∑ x ∈ A, μ x)
    (hB : 1 ≤ B * (∑ x ∈ A, μ x)) :
    U / (∑ x ∈ A, μ x) * returnOccupation P A μ H ≤ U * B := by sorry
