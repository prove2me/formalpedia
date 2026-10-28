-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryPathMoment_stationary_square_succ
-- name    : CountingMatroid.Analysis.StationaryPathMoment.stationary_square_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:22:19.743752+00:00
-- url     : https://prove2.me/theorems/3285e601-55de-4d97-b1d8-2f1b7edcce18
-- title:
--   Recursion for the stationary second moment of an observation sum
-- statement:
--   For a finite state space $\Omega$ with decidable equality and a stochastic matrix $P$, an $N$-transition path is $\gamma=(x_0,\ldots,x_N)\in\Omega^{N+1}$. Define
--   $$p_N(\gamma)=\prod_{i=0}^{N-1}P(x_i,x_{i+1}),\qquad A_N(g,\gamma)=\sum_{i=0}^{N-1}g(x_i).$$
--   Thus the last transition contributes to the path weight but its endpoint is not an observation.
--   Let $\pi$ be a stationary probability distribution for $P$, let $g:\Omega\to\mathbb R$, and define
--   $$V_N=\sum_{\gamma\in\Omega^{N+1}}\pi(x_0)p_N(\gamma)A_N(g,\gamma)^2,\qquad\langle f,h\rangle_\pi=\sum_x\pi(x)f(x)h(x).$$
--   For every $N\in\mathbb N$,
--   $$V_{N+1}=V_N+\langle g,g\rangle_\pi+2\sum_{t=0}^{N-1}\langle g,P^{t+1}g\rangle_\pi.$$
--   This exact recursion separates the new observation’s squared contribution from its correlations with the suffix.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryPathMoment.lean#L129-L181

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

theorem CountingMatroid.Analysis.StationaryPathMoment.stationary_square_succ [DecidableEq Ω] (π : FinDist Ω)
    (P : FinChain Ω) (hst : Stationary π P) (g : Ω → ℝ) (N : ℕ) :
    pathSquaredSum π P g (N + 1) = pathSquaredSum π P g N + ip π g g +
      2 * ∑ t ∈ Finset.range N, ip π g ((P.iter (t + 1)).act g) := by sorry
