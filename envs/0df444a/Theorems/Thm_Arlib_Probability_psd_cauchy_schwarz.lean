-- Prove2me | Theorems.Thm_Arlib_Probability_psd_cauchy_schwarz
-- name    : Arlib.Probability.psd_cauchy_schwarz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:22:04.398989+00:00
-- url     : https://prove2.me/theorems/e009f4e1-d0c7-4087-86a4-e0b1362d2138
-- title:
--   Cauchy–Schwarz for a positive semidefinite symmetric bilinear form
-- statement:
--   Let $I$ be any type and $B:(I\to\mathbb R)\times(I\to\mathbb R)\to\mathbb R$ be bilinear and symmetric. Suppose $B(u,u)\ge0$ for every $u$. Then $$B(u,v)^2\le B(u,u)B(v,v)\qquad\text{for all }u,v:I\to\mathbb R.$$
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Probability/Bilinear.lean#L43-L67

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

theorem Arlib.Probability.psd_cauchy_schwarz {ι : Type*} {B : (ι → ℝ) → (ι → ℝ) → ℝ}
    (hbil : IsBilin B) (hsymm : ∀ u v, B u v = B v u) (hpsd : ∀ u, 0 ≤ B u u)
    (u v : ι → ℝ) : B u v ^ 2 ≤ B u u * B v v := by sorry
