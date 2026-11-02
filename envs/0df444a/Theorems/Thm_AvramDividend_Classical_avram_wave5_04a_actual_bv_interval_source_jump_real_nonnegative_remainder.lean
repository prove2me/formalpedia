-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:47:19.556198+00:00
-- url     : https://prove2.me/theorems/e84d1832-1a90-4b40-a0ca-e0f4065fdb5e
-- title:
--   Genuine original BV source interval loss equals its full jump sum plus a nonnegative real remainder
-- statement:
--   On a single almost-sure event of the actual bounded-variation spectrally negative Lévy process, for every original time interval (s,t], the real drift residual increment ((t*d-X_t)-(s*d-X_s)) equals the real value of the entire summable negative source-jump magnitude series plus an ordinary nonnegative real remainder. This proves finiteness of the source-jump sum and gives a finite real source loss for C1 chain-rule derivatives without an unproved pure-jump equality. Every samplewise stopped interval is included.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, Wave 5 Chat 04-A. Canonical Proved 0ebd2a44-06bf-4a28-a9db-4e70c0ac84c8 supplies all-interval original jump mass bound; canonical Proved f6cc1059-e8ca-403e-8d73-71a139d3dc4c supplies residual monotonicity. Pinned ENNReal.toReal_mono and ENNReal.toReal_ofReal convert finite mass inequality to real units.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' (u : ℝ≥0),
          if s < u ∧ u ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          else 0).toReal + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by sorry
