-- Prove2me | Theorems.Thm_Complex_exists_forall_norm_pow_sub_one_lt
-- name    : Complex.exists_forall_norm_pow_sub_one_lt
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:16.456054+00:00
-- url     : https://prove2.me/theorems/e5291bfe-25ca-4c2c-a864-da8cc2e9792d
-- title:
--   Simultaneous near-identity powers on a finite complex torus
-- statement:
--   For any finite family of complex numbers uᵢ with ‖uᵢ‖ = 1, every ε > 0, and every natural lower bound N, there is a positive integer n ≥ N such that ‖uᵢⁿ − 1‖ < ε for all i.
-- source:
--   Upstream https://github.com/teal-sea/zeta-lab/tree/main/lean/ZetaLean/PrivateStock (Apache-2.0); checked task source research/hec-lean433/ZetaLean/PrivateStock/NormLeOfForallNormSumPowLe.lean lines 35–74; SHA256 46371ca5e2adeb988f81187288be412356764f1d5022be76089c70d49d439207.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Complex
end Complex
namespace Filter
end Filter
namespace Finset
end Finset
namespace Topology
end Topology


/-!
# Bounding the terms of a family from bounds on its power sums

If `ω : ι → ℂ` is a finite family of complex numbers whose power sums satisfy
`‖∑ i, ω i ^ k‖ ≤ C * B ^ k` for every `k > 0`, then every `ω i` satisfies `‖ω i‖ ≤ B`.

This is the standard "no cancellation in the long run" argument: writing `M` for the largest
modulus occurring in the family and `S` for the set of indices attaining it, the numbers
`ω i / M` for `i ∈ S` lie on the unit circle, so by compactness of the torus there are
arbitrarily large exponents `n` for which all the `(ω i / M) ^ n`, `i ∈ S`, are simultaneously
close to `1`.  For such `n` the maximal terms of `∑ i, ω i ^ n` add up essentially without
cancellation, forcing `M ^ n ≲ C * B ^ n`, which is impossible for large `n` unless `M ≤ B`.
-/
set_option autoImplicit false
open Finset Filter Topology
open Complex

theorem Complex.exists_forall_norm_pow_sub_one_lt {ι : Type*} [Fintype ι] {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by sorry
