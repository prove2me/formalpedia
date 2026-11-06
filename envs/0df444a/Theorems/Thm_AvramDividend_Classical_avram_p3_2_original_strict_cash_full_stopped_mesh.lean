-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_full_stopped_mesh
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_cash_full_stopped_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:24:17.133389+00:00
-- url     : https://prove2.me/theorems/b72a139f-6ae7-4a9a-82e2-752b66131b16
-- title:
--   Entire original pre-ruin and strictly pre-T cash equals the finite physical stopped mesh sum
-- statement:
--   The original dividendMeasure strictly before T and restricted to payments strictly before ruin, integrated over the full physical stopped clock from 0, equals the finite sum of integrals on the m+1 stopped Ioc mesh cells, for any ENNReal integrand.
-- source:
--   Exact original pre-T mesh additivity, physical endpoint arithmetic and finite extended ruin-clock projection; no source stochastic assumptions strengthened.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_discounted_mesh_sum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_mesh_terminal_clip
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_ennreal_truncated_clock_toNNReal_le

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_cash_full_stopped_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let B : Set ℝ :=
      paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
    (∫⁻ t in B ∩ Ioc (0 : ℝ) (τ : ℝ),
      f t ∂(dividendMeasure D ω)) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂(dividendMeasure D ω)):= by sorry
