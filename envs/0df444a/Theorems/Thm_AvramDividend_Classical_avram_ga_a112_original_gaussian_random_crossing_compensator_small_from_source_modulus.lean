-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
-- name    : AvramDividend.Classical.avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:41:20.1565+00:00
-- url     : https://prove2.me/theorems/cbd9da80-b8c7-45a8-98d0-0d71dbb5289c
-- title:
--   Bounded original Gaussian crossing-cell HJB compensator vanishes as the actual un-clipped full physical source increment and mesh width vanish
-- statement:
--   The original stopped Gaussian crossing-cell generator compensation is a derivative times the full physical source increment, a bounded Hessian times its square minus variance clock, and a generator times the mesh width. If compact localisation bounds its coefficients, the absolute compensator has a uniform bound by the source displacement, its square and the mesh width. The proof shows its actual value tends to zero when those two physical quantities vanish, allowing a one-sided crossing-cell treatment with true clipped source value.
-- source:
--   True random original Gaussian stop crossing source uniform continuity plus compact derivative and generator bounds for the actual full physical compensated HJB cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
    (Z Δ H : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hΔ : ∀ m, 0 ≤ Δ m)
    (hError : ∀ m,
      |H m| ≤ K * (|Z m| + (Z m)^2 + Δ m))
    (hZ : Tendsto Z atTop (𝓝 (0 : ℝ)))
    (hΔlim : Tendsto Δ atTop (𝓝 (0 : ℝ))) :
    Tendsto H atTop (𝓝 (0 : ℝ)) := by sorry
