-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_centered_increment_covariance_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:52:14.662286+00:00
-- url     : https://prove2.me/theorems/f2155d3f-c49a-49ad-845c-244cacd42c27
-- title:
--   Consecutive actual Levy source increments centred by their means have zero covariance
-- statement:
--   On the original Ω and P, covariance of two consecutive independently incremented canonical X cells is zero after separately subtracting each cell's actual mean, requiring only L1 integrability. The product integral is justified by original IndepFun, measurability of centring maps, and pinned product-integral factorisation.
-- source:
--   W7-06 genuine two-cell source centred L2 orthogonality without zero drift assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P) :
    (∫ ω,
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P)) *
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P)) ∂P) = 0 := by sorry
