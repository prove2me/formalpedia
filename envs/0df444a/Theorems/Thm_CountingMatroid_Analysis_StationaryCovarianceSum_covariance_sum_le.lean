-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryCovarianceSum_covariance_sum_le
-- name    : CountingMatroid.Analysis.StationaryCovarianceSum.covariance_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:22:08.129851+00:00
-- url     : https://prove2.me/theorems/2afc0f26-308e-4644-8e2b-045b01b262ab
-- title:
--   A dual energy bound controls every finite covariance sum
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $\pi$ a probability distribution on $\Omega$, and $P$ a stochastic transition matrix. Write $(Pf)(x)=\sum_yP(x,y)f(y)$, let $P^t$ denote the $t$th transition power with $P^0=I$, and define
--   $$\langle f,h\rangle_\pi=\sum_x\pi(x)f(x)h(x),\qquad\mathcal E(f,h)=\langle f,h-Ph\rangle_\pi.$$
--   Assume reversibility, $\pi(x)P(x,y)=\pi(y)P(y,x)$, and positive semidefiniteness, $\langle f,Pf\rangle_\pi\ge0$ for all real functions $f$. Let $g:\Omega\to\mathbb R$ and $C\ge0$ satisfy
--   $$\langle g,H\rangle_\pi^2\le C\mathcal E(H,H)\qquad\text{for every }H:\Omega\to\mathbb R.$$
--   Then for every $N\in\mathbb N$,
--   $$\sum_{t=0}^{N-1}\langle g,P^tg\rangle_\pi\le C.$$
--   This finite-sum estimate supplies the correlation control used to bound stationary observation errors.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryCovarianceSum.lean#L83-L129

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

theorem CountingMatroid.Analysis.StationaryCovarianceSum.covariance_sum_le {π : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible π P) (hpsd : NonnegDefinite π P)
    (g : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdual : ∀ H : Ω → ℝ, (ip π g H) ^ 2 ≤ C * dirichlet π P H H)
    (N : ℕ) :
    (∑ t ∈ Finset.range N, ip π g ((P.iter t).act g)) ≤ C := by sorry
