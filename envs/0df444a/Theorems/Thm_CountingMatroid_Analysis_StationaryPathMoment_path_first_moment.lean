-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryPathMoment_path_first_moment
-- name    : CountingMatroid.Analysis.StationaryPathMoment.path_first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:18:20.330312+00:00
-- url     : https://prove2.me/theorems/d6b9274b-e2f6-4b26-a742-5d9cadce32b2
-- title:
--   The first path moment is a sum of iterated transition actions
-- statement:
--   For a finite state space $\Omega$ with decidable equality and a stochastic matrix $P$, an $N$-transition path is $\gamma=(x_0,\ldots,x_N)\in\Omega^{N+1}$. Define
--   $$p_N(\gamma)=\prod_{i=0}^{N-1}P(x_i,x_{i+1}),\qquad A_N(g,\gamma)=\sum_{i=0}^{N-1}g(x_i).$$
--   Thus the last transition contributes to the path weight but its endpoint is not an observation.
--   Let $g,w:\Omega\to\mathbb R$ be arbitrary functions and $N\in\mathbb N$. The initial weights $w$ need not be nonnegative or normalized. Then
--   $$\sum_{\gamma\in\Omega^{N+1}}w(x_0)p_N(\gamma)A_N(g,\gamma)=\sum_{t=0}^{N-1}\sum_{x\in\Omega}w(x)(P^tg)(x),$$
--   where $(P^tg)(x)=\sum_yP^t(x,y)g(y)$. This expresses a finite weighted observation sum through the transition powers, including signed initial weights.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryPathMoment.lean#L73-L121

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

theorem CountingMatroid.Analysis.StationaryPathMoment.path_first_moment [DecidableEq Ω] (P : FinChain Ω)
    (g w : Ω → ℝ) (N : ℕ) :
    (∑ path : Fin (N + 1) → Ω,
      w (path 0) * pathWeight P N path * observationSum g N path) =
      ∑ t ∈ Finset.range N, ∑ x, w x * (P.iter t).act g x := by sorry
