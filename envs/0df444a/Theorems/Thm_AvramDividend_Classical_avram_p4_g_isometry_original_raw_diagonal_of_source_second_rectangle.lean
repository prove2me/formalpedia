-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:22:23.297199+00:00
-- url     : https://prove2.me/theorems/9b483610-7d5c-4b8a-9305-66dc06fec7c4
-- title:
--   Original physical finite negative-band predictable diagonal L2 identity from source conditional second rectangle law
-- statement:
--   For the actual intrinsic Lévy count on the original X/P/raw F and finite separated negative mark band, conditional on the exact source diagonal second-moment law P[(N_X-r)^2 | F_s] = r and explicit moment integrability, every predictable H obeys E[(H(N_X-r))^2] = r E[H^2]. This isolates the precise missing second-moment premise without asserting stationary means imply Poisson variance, nor claiming infinite-band or stopped results.
-- source:
--   Pinned Mathlib integral_condExp and condExp_mul_of_stronglyMeasurable_left; exact original source physical-count equality with X.nu rate and explicit source conditional second-moment assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hRate : r = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    (hSecond : P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕 s]
       =ᵐ[P] (fun _ => r))
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hHSqInt : Integrable (fun ω => (H ω) ^ 2) P)
    (hWeightedSqInt : Integrable
      (fun ω => (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) P) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by
 sorry
