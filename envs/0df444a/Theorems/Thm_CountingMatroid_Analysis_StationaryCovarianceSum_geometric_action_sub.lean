-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryCovarianceSum_geometric_action_sub
-- name    : CountingMatroid.Analysis.StationaryCovarianceSum.geometric_action_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:18:17.56964+00:00
-- url     : https://prove2.me/theorems/67820f60-bfdf-495d-aac9-c86d32ce9274
-- title:
--   A finite geometric sum of Markov operators telescopes
-- statement:
--   Let $\Omega$ be a finite state set and let $P$ be a Markov transition matrix on $\Omega$, so $P(x,y)\ge0$ and $\sum_yP(x,y)=1$. For $g:\Omega\to\mathbb R$, define $(Pg)(x)=\sum_yP(x,y)g(y)$ and write $P^t$ for the $t$-fold iterate, with $P^0g=g$. For every $N\in\mathbb N$, the following equality holds as an identity of functions on $\Omega$: $$\sum_{t=0}^{N-1}P^tg-P\left(\sum_{t=0}^{N-1}P^tg\right)=g-P^Ng.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryCovarianceSum.lean#L56-L81

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
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

namespace CountingMatroid.Analysis.StationaryCovarianceSum
end CountingMatroid.Analysis.StationaryCovarianceSum
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Finite covariance sums for reversible positive semidefinite chains. The
finite geometric sum replaces the inverse and infinite series in the paper,
so the argument also applies to stationary laws with zero-weight states.
-/
namespace CountingMatroid.Analysis.StationaryCovarianceSum
end CountingMatroid.Analysis.StationaryCovarianceSum
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryCovarianceSum

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.StationaryCovarianceSum.geometric_action_sub (P : FinChain Ω) (g : Ω → ℝ) (N : ℕ) :
    (fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x) -
      P.act (fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x) =
        g - (P.iter N).act g := by sorry
