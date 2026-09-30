-- Prove2me | Theorems.Thm_Complex_summable_taylorSeries_neg_log
-- name    : Complex.summable_taylorSeries_neg_log
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:20.983988+00:00
-- url     : https://prove2.me/theorems/54cd425f-ed32-4415-9c21-a44c4813b11e
-- title:
--   Absolute summability of the logarithm Taylor family
-- statement:
--   Let $(r_i)_{i\in I}$ be a summable complex family, and assume $|r_i|<1$ for every $i$. Its logarithmic Taylor terms are jointly absolutely summable:
--
--   $$
--   \sum_{(i,e)\in I\times\mathbb N}\left|\frac{r_i^{e+1}}{e+1}\right|<\infty.
--   $$
--
--   Joint summability permits regrouping the logarithmic expansion by index or by exponent.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Complex/LogBounds.lean#L36-L60), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Complex/LogBounds.lean#L36-L60

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Taylor series of `-log (1 - ·)` summed over a family

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
-/

 section

namespace Complex
end Complex
section Complex
open Complex

theorem Complex.summable_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : _root_.Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    _root_.Summable fun ie : ι × ℕ ↦ r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) := by sorry
