-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_ofReal_geometric_tsum_unshifted
-- name    : AvramDividend.Classical.chat12_ofReal_geometric_tsum_unshifted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:29:47.512594+00:00
-- url     : https://prove2.me/theorems/dd8ab629-e2c5-4361-811f-0e10ae6e950b
-- title:
--   Unshifted extended-real geometric sum with real nonnegative record payments
-- statement:
--   For nonnegative real epsilon and p, summing the ENNReal embeddings of epsilon*p^n over all n yields ENNReal.ofReal epsilon multiplied by (1 - ENNReal.ofReal p)^(-1). The identity holds in extended nonnegative reals, including divergent series, and is suitable for converting an upper expected-record geometric budget into a closed-form renewal bound. The proof invokes the pinned Mathlib ENNReal.tsum_geometric and ENNReal.tsum_mul_left declarations.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.Real

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_ofReal_geometric_tsum_unshifted (ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) :
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) =
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by sorry
