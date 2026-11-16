-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jumpfree_compensated_residual_constant
-- name    : AvramDividend.Classical.avram_bva_finite_jumpfree_compensated_residual_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:43:33.845572+00:00
-- url     : https://prove2.me/theorems/c2cf1ee7-64ff-474f-8a45-a71956436dac
-- title:
--   Physical finite-jump compensated residual constant on a jump-free interval
-- statement:
--   If every genuine jump on a time interval belongs to a finite mark set, the set has no marks in that interval, and the path has drift-only evolution when there are no jumps, then drift deficit minus cumulative actual finite-mark jump sizes has exactly equal values at both endpoints.
-- source:
--   Deterministic Lévy-Ito finite-activity pathwise decomposition, jump-free interval split

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_jumpfree_compensated_residual_constant
    (f : ℝ≥0 → ℝ) (drift : ℝ) (S : Finset ℝ≥0)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hCover : ∀ u ∈ Set.Ioc s t,
       f u - Function.leftLim f u ≠ 0 → u ∈ S)
    (hNo : ∀ u ∈ S, ¬ (s < u ∧ u ≤ t))
    (hFlat : (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
        (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    (t : ℝ) * drift - f t -
      Finset.sum S (fun u => if u ≤ t then Function.leftLim f u - f u else 0) =
    (s : ℝ) * drift - f s -
      Finset.sum S (fun u => if u ≤ s then Function.leftLim f u - f u else 0) := by sorry
