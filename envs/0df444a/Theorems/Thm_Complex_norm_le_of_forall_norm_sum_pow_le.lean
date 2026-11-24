-- Prove2me | Theorems.Thm_Complex_norm_le_of_forall_norm_sum_pow_le
-- name    : Complex.norm_le_of_forall_norm_sum_pow_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:19.302295+00:00
-- url     : https://prove2.me/theorems/c551c7a1-2672-426f-8778-75f2cbc64149
-- title:
--   Exponential power-sum bounds control each complex modulus
-- statement:
--   Let ωᵢ be a finite family of complex numbers and let B > 0. If a real constant C satisfies ‖Σᵢωᵢᵏ‖ ≤ C·Bᵏ for every positive integer k, then ‖ωᵢ‖ ≤ B for every index i.
-- source:
--   Upstream https://github.com/teal-sea/zeta-lab/tree/main/lean/ZetaLean/PrivateStock (Apache-2.0); checked task source research/hec-lean433/ZetaLean/PrivateStock/NormLeOfForallNormSumPowLe.lean lines 76–217; SHA256 46371ca5e2adeb988f81187288be412356764f1d5022be76089c70d49d439207.

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

theorem Complex.norm_le_of_forall_norm_sum_pow_le {ι : Type*} [Fintype ι] {ω : ι → ℂ} {B C : ℝ}
    (hB : 0 < B) (h : ∀ k : ℕ, 0 < k → ‖∑ i, ω i ^ k‖ ≤ C * B ^ k) (i : ι) :
    ‖ω i‖ ≤ B := by sorry
