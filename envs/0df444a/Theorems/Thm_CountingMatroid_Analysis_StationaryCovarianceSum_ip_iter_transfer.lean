-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryCovarianceSum_ip_iter_transfer
-- name    : CountingMatroid.Analysis.StationaryCovarianceSum.ip_iter_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:20:31.388933+00:00
-- url     : https://prove2.me/theorems/a51d43bb-3812-4df6-98b1-966987b57032
-- title:
--   Reversibility transfers every kernel power across the weighted inner product
-- statement:
--   Let $\Omega$ be finite, $\pi$ a probability distribution, and $P$ a Markov kernel. Write $(Pf)(x)=\sum_yP(x,y)f(y)$ and $\langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)$. Assume detailed balance $\pi(x)P(x,y)=\pi(y)P(y,x)$. For all real state functions $f,g$ and $t\in\mathbb N$, $$\langle f,P^tg\rangle_\pi=\langle P^tf,g\rangle_\pi.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryCovarianceSum.lean#L26-L41

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

theorem CountingMatroid.Analysis.StationaryCovarianceSum.ip_iter_transfer {π : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible π P) (f g : Ω → ℝ) (t : ℕ) :
    ip π f ((P.iter t).act g) = ip π ((P.iter t).act f) g := by sorry
