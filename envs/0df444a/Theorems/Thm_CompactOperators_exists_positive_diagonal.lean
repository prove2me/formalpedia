-- Prove2me | Theorems.Thm_CompactOperators_exists_positive_diagonal
-- name    : CompactOperators.exists_positive_diagonal
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:13.344364+00:00
-- url     : https://prove2.me/theorems/62b0291d-8553-4c89-bd4b-676becd470df
-- title:
--   Positive bounded diagonal multipliers on Hilbert sums
-- statement:
--   Let $(d_i)_{i\in I}$ be a uniformly bounded family of nonnegative real numbers. On the real or complex Hilbert space $\ell^2(I)$, there is a positive bounded linear operator $D$ whose $i$th coordinate is $d_i x_i$. The index set can be arbitrary, including empty. This provides the diagonal construction for square roots of compact positive operators.
-- source:
--   Standard positive diagonal multiplier construction; used in the compact positive-operator square-root proof.

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Lp.lpHolder

universe u v

namespace CompactOperators

theorem exists_positive_diagonal {𝕜 : Type v} [RCLike 𝕜] {ι : Type u}
    (d : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hd₀ : ∀ i, 0 ≤ d i) (hdK : ∀ i, d i ≤ K) :
    ∃ D : lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2,
      D.IsPositive ∧ ∀ x i, D x i = (d i : 𝕜) * x i := by sorry

end CompactOperators
