-- Prove2me | Theorems.Thm_AvramDividend_Classical_nnreal_natCaps_cofinal
-- name    : AvramDividend.Classical.nnreal_natCaps_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:56.706463+00:00
-- url     : https://prove2.me/theorems/61fc3090-b59b-4336-9a50-cd51cf2dc958
-- title:
--   Natural-number deterministic horizons are strictly cofinal in nonnegative real time
-- statement:
--   Every finite nonnegative real time t lies strictly below a natural-number horizon cast to ℝ≥0. Prove this by the Archimedean property of real numbers and cast the resulting strict inequality into ℝ≥0. The theorem allows the unbounded-horizon reflected first closed-level hitting-time construction to use canonical integer caps H_n=n, instead of requiring an externally chosen cofinal horizon sequence.
-- source:
--   Pinned Mathlib.Algebra.Order.Archimedean.Defs.exists_nat_gt and casts between real and nonnegative real.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.nnreal_natCaps_cofinal :
    ∀ t : ℝ≥0, ∃ n : ℕ, t < (n : ℝ≥0) := by sorry
