-- Prove2me | Theorems.Thm_Arlib_MarkovChains_comp_stationary
-- name    : Arlib.MarkovChains.comp_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:04:59.835139+00:00
-- url     : https://prove2.me/theorems/a4d5b8a1-b089-4c27-b391-a7ebe13e009e
-- title:
--   A common stationary distribution is stationary for a composite kernel
-- statement:
--   Let $\Omega$ be finite, let $\mu$ be a probability distribution, and let $P,Q$ be Markov kernels with $\mu P=\mu$ and $\mu Q=\mu$. Define $(PQ)(x,z)=\sum_yP(x,y)Q(y,z)$. Then $$\mu(PQ)=\mu.$$
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/MarkovChains/Techniques/Comparison.lean#L183-L198

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
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

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Comparison of chains, and the gap of an iterate

Almost no spectral gap is ever computed.  What one does instead is *transfer* a
gap: take a chain whose Poincaré constant is known, show that the chain one
actually cares about has a Dirichlet form at least comparable to it, and read
off a gap for free.  This is the comparison method, and it is the reason a
module in `Chains/` can bound a gap without ever evaluating a sum.

The method is completely elementary here, and that is the point of the pair form
`dirichlet_self_eq_pair`: both Dirichlet forms are finite sums
`½ ∑_{x,y} μ(x) · K(x,y) · (f x - f y)²` over the *same* index set with the
*same* weights `μ(x) (f x - f y)²`, so domination of one form by the other is a
term-by-term inequality between the kernels — and only off the diagonal, since
the diagonal terms carry the factor `(f x - f x)² = 0`.

* `DirichletLe μ P Q A` — `ℰ_P(f) ≤ A · ℰ_Q(f)` for every `f`; "`Q` dominates
  `P` with constant `A`".  Reflexive with `A = 1`, and composes by multiplying
  constants.
* `spectralGapAtLeast_of_dirichletLe` — **the comparison theorem**: if `Q`
  dominates `P` with constant `A > 0` and `P` has gap `γ`, then `Q` has gap
  `γ / A`.  It is `Q` that inherits the gap, because `Q`'s Dirichlet form is the
  larger one.
* `dirichletLe_of_entrywise` — **the practical criterion**: for `μ` stationary
  for both chains, an entrywise bound `P(x,y) ≤ A · Q(x,y)` *off the diagonal*
  suffices.  The diagonal is genuinely irrelevant, which is what makes the
  criterion usable: laziness, holding probabilities and self-loops may be
  changed at will.
* `absSpectralBound_mono`, `comp_reversible`, `iter_reversible` — the small API
  needed to iterate.
* `absSpectralBound_iter` — **the absolute spectral bound of an iterate**:
  `AbsSpectralBound μ P c` with `0 ≤ c` gives `AbsSpectralBound μ (P^t) (c^t)`,
  and hence `spectralGapAtLeast_iter`, the Poincaré inequality for `P^t` with
  constant `1 - c^t`.  The proof runs the operator bound `ip_act_sq_le` `t`
  times to control `‖P^t f‖`, then applies Cauchy–Schwarz once; no eigenvalue,
  and in particular no "the eigenvalues of `P^t` are the `t`-th powers of those
  of `P`", is involved.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains
end Arlib.MarkovChains
open Arlib Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Domination of Dirichlet forms -/











/-! ## Transfer of the spectral gap

The comparison theorem itself, which is one line of division once the two
Poincaré inequalities are lined up. -/



/-! ## The entrywise criterion

In practice one never verifies `DirichletLe` directly; one compares the two
transition matrices entry by entry.  The pair form turns the comparison of the
forms into exactly that, and only off the diagonal: the terms with `x = y` carry
the factor `(f x - f x)² = 0` on both sides. -/







/-! ## Monotonicity of the absolute spectral bound -/



/-! ## Stationarity and reversibility of composites

Stationarity passes to any composite.  Reversibility does *not*: detailed balance
for `P ∘ₖ Q` unwinds to `μ(x) (PQ)(x,z) = μ(z) (QP)(z,x)`, so one needs the two
chains to commute.  They do in the case that matters, `P` with its own iterate,
which is `FinKernel.iter_succ'`. -/

theorem Arlib.MarkovChains.comp_stationary {μ : FinDist Ω} {P Q : FinChain Ω}
    (hP : Stationary μ P) (hQ : Stationary μ Q) : Stationary μ (P ∘ₖ Q) := by sorry
