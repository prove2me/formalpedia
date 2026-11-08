-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_uniform_positive_prejump_risk_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_original_uniform_positive_prejump_risk_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:26:12.912634+00:00
-- url     : https://prove2.me/theorems/484e5768-9476-435b-8386-025392d51ce3
-- title:
--   Original pre-right-payment reserve equals risk reserve simultaneously on all positive uniform-grid cells
-- statement:
--   For the authentic original spectrally negative Levy reserve and an adapted dividend strategy, the left limit of initial surplus plus process minus the right dividend limit agrees almost surely with the original prepayment risk reserve simultaneously at all strictly positive points of all canonical refining uniform grids. Positivity of each nonzero grid point follows from the exact physical grid formula. The common full-measure event is obtained by a countable intersection across grid rows, using the existing accepted original single-sequence prepayment lemma. Time zero remains separate and no stopping or dividend atom is silently identified with a positive clock.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, triangular-grid prepayment reserve, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_uniform_positive_prejump_risk_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i : ℕ,
      Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n (i + 1)) =
        riskProcess X x D (u n (i + 1)) ω := by sorry
