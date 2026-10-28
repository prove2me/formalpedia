-- Prove2me | Theorems.Thm_Arlib_Probability_isBilin_weighted
-- name    : Arlib.Probability.isBilin_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:07:31.951299+00:00
-- url     : https://prove2.me/theorems/15f2930f-12a9-44aa-a7e9-da0d95637a8c
-- title:
--   Every finite weighted pairing is bilinear
-- statement:
--   Let $I$ be a finite type and $w:I\to\mathbb R$ arbitrary. Define $$B(u,v)=\sum_{i\in I}w(i)u(i)v(i)\qquad(u,v\in\mathbb R^I).$$ Then $B$ is linear in each of its two arguments. In particular, for real scalars $a,b$, $$B(au+bv,z)=aB(u,z)+bB(v,z),\qquad B(z,au+bv)=aB(z,u)+bB(z,v).$$
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Probability/Bilinear.lean#L69-L83

import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
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

namespace Arlib
end Arlib
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Cauchy–Schwarz for a positive semidefinite symmetric bilinear form

The spectral arguments in the local-to-global machinery repeatedly need the
following completely elementary fact: a symmetric bilinear form `B` on a real
vector space which satisfies `0 ≤ B u u` also satisfies

  `B u v ^ 2 ≤ B u u * B v v`.

The usual textbook route is via eigenvalues; the route taken here is the
discriminant of the nonnegative quadratic `t ↦ B (u + t • v) (u + t • v)`, which
needs no spectral theory at all and hence transfers verbatim to Lean.

We state it for a form on functions `ι → ℝ`, which is the only setting used
downstream (`L²(μ)` inner products, and the forms `⟪·, P ·⟫_μ` attached to a
reversible chain).  Two consequences are packaged for direct use:

* `psd_cauchy_schwarz` — the inequality itself;
* `norm_sq_le_of_psd_le` — if `B` is PSD and `B u u ≤ c * Q u u` for a PSD `Q`,
  then the "operator norm" bound `Q (Bop u) (Bop u) ≤ c ^ 2 * Q u u` follows.
  (Stated concretely at the point of use; here we only supply the core lemma.)

Everything is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability
end Arlib.Probability
open Arlib Arlib.Probability

theorem Arlib.Probability.isBilin_weighted {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    IsBilin (fun u v => ∑ x, w x * u x * v x) := by sorry
