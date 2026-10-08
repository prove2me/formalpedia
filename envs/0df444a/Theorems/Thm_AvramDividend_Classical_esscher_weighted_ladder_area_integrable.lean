-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_ladder_area_integrable
-- name    : AvramDividend.Classical.esscher_weighted_ladder_area_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:52:14.009234+00:00
-- url     : https://prove2.me/theorems/044d610e-aba4-40c3-ada9-5a77fae84169
-- title:
--   Original Lévy integrability implies finiteness of the Esscher-weighted truncated ladder-height area
-- statement:
--   For a positive-jump Lévy measure μ satisfying its truncated quadratic integrability condition, the outer integral of the Esscher-damped truncated ladder-height area exp(−φz)∫₀ᶻmin(1,t)dt is finite. The interval-area inequality bounds its integrand by exp(−φz)min(z²,z); the latter has already been isolated as an integrable jump-kernel lemma. This is precisely the right-hand side of the Tonelli exchange needed to show the descending ladder-height Lévy measure obeys the subordinator first-moment integrability condition.
-- source:
--   esscher_tilted_tail_area_integrable and ladder_height_truncated_area_interval_bound; pinned MeasureTheory.lintegral_mono_ae and ENNReal.ofReal_le_ofReal.

import Mathlib
open MeasureTheory intervalIntegral Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_weighted_ladder_area_integrable
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-(φ * z)) *
        (∫ t in (0 : ℝ)..z, min 1 t)) ∂μ) < ⊤ := by sorry
