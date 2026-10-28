-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StationaryPathMoment_path_mass
-- name    : CountingMatroid.Analysis.StationaryPathMoment.path_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:12:54.816981+00:00
-- url     : https://prove2.me/theorems/653714e0-9254-4ec1-b3ff-3bf9e910891e
-- title:
--   Summing finite path weights preserves the initial total mass
-- statement:
--   Let $\Omega$ be finite, $P$ a Markov kernel on $\Omega$, $N\in\mathbb N$, and $w:\Omega\to\mathbb R$ arbitrary. For $x=(x_0,\ldots,x_N)$ put $W_P(x)=\prod_{a=0}^{N-1}P(x_a,x_{a+1})$. Then $$\sum_{x_0,\ldots,x_N}w(x_0)W_P(x)=\sum_{x_0}w(x_0).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryPathMoment.lean#L55-L71

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

theorem CountingMatroid.Analysis.StationaryPathMoment.path_mass (P : FinChain Ω) (N : ℕ) (w : Ω → ℝ) :
    (∑ path : Fin (N + 1) → Ω, w (path 0) * pathWeight P N path) = ∑ x, w x := by sorry
