-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryPathMoment_stationary_average_le_of_covariance
-- name    : CountingMatroid.Analysis.StationaryPathMoment.stationary_average_le_of_covariance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:26:42.5924+00:00
-- url     : https://prove2.me/theorems/eeb5a68e-5e90-4920-be83-2a0dd807a401
-- title:
--   Stationary sample-average error from finite covariance bounds
-- statement:
--   For a finite state space $\Omega$ with decidable equality and a stochastic matrix $P$, an $N$-transition path is $\gamma=(x_0,\ldots,x_N)\in\Omega^{N+1}$. Define
--   $$p_N(\gamma)=\prod_{i=0}^{N-1}P(x_i,x_{i+1}),\qquad A_N(g,\gamma)=\sum_{i=0}^{N-1}g(x_i).$$
--   Thus the last transition contributes to the path weight but its endpoint is not an observation.
--   Let $\pi$ be stationary for $P$, let $G:\Omega\to\mathbb R$, and put $\mu=\sum_x\pi(x)G(x)$ and $g=G-\mu$. Let $C\in\mathbb R$ satisfy
--   $$\sum_{t=0}^{m-1}\langle g,P^tg\rangle_\pi\le C\qquad\text{for every }m\in\mathbb N,$$
--   where $\langle f,h\rangle_\pi=\sum_x\pi(x)f(x)h(x)$. Then for every positive integer $N$,
--   $$\sum_{\gamma\in\Omega^{N+1}}\pi(x_0)p_N(\gamma)\left(\frac1N\sum_{i=0}^{N-1}G(x_i)-\mu\right)^2\le\frac{2C}{N}.$$
--   This bounds the mean squared error of the correlated stationary observations without requiring independence.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryPathMoment.lean#L201-L235

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_StationaryPathMoment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fin.Tuple.Basic
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

namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Finite product-path expectations and moments. The last transition is unused
by the observations, matching the stationary observation experiment.
-/
namespace CountingMatroid.Analysis.StationaryPathMoment
end CountingMatroid.Analysis.StationaryPathMoment
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryPathMoment

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω]

theorem CountingMatroid.Analysis.StationaryPathMoment.stationary_average_le_of_covariance [DecidableEq Ω] (π : FinDist Ω)
    (P : FinChain Ω) (hst : Stationary π P) (G : Ω → ℝ) (C : ℝ)
    (hcov : ∀ N, (∑ t ∈ Finset.range N,
      ip π (fun x => G x - Ex π G)
        ((P.iter t).act (fun x => G x - Ex π G))) ≤ C)
    (N : ℕ) (hN : 0 < N) :
    (∑ path : Fin (N + 1) → Ω,
      (π (path 0) * ∏ i : Fin N, P (path i.castSucc) (path i.succ)) *
        ((∑ i : Fin N, G (path i.castSucc)) / (N : ℝ) - Ex π G) ^ 2) ≤
      2 * C / (N : ℝ) := by sorry
