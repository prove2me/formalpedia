-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a65_ofReal_liminf_from_real_eventual_lower
-- name    : AvramDividend.Classical.avram_bva_a65_ofReal_liminf_from_real_eventual_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:00:36.033148+00:00
-- url     : https://prove2.me/theorems/187185a0-a28f-46ee-b9c7-f3dfd4560aa6
-- title:
--   ENNReal liminf lower bound from eventually arbitrary positive real epsilon lower estimates
-- statement:
--   Pure order topology: if for every positive epsilon a real sequence is eventually greater than a minus epsilon, the ENNReal liminf of its nonnegative embeddings is at least the embedding of a. Essential analytic bridge to combine an original strict physical discounted dividend cash prefix with the correctly prepayment terminal lower limit, without requiring full terminal equality or global martingale integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a65_ofReal_liminf_from_real_eventual_lower
    (a : ℝ) (u : ℕ → ℝ)
    (hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (atTop : Filter ℕ), a - ε < u n) :
    ENNReal.ofReal a ≤ liminf (fun n : ℕ => ENNReal.ofReal (u n)) atTop := by sorry
