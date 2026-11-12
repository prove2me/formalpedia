-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_largejump_interval_difference
-- name    : AvramDividend.Classical.avram_ja18h_original_largejump_interval_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:40:11.9562+00:00
-- url     : https://prove2.me/theorems/e7553758-29a5-43fa-aa22-7e3a10ff6d9e
-- title:
--   Original signed large-jump cumulative difference equals its physical (s,t] window integral
-- statement:
--   Prove pathwise, for original cadlag spectrally negative Lévy X and any s≤t, that the difference between the original signed large-negative jump integrals on (0,t] and (0,s] equals the integral on (s,t]. The magnitude≥1 jumps are locally finite on every cadlag path, so signed integrals are finite and countably additive. This pure source-measure ledger is independent of future-path measurability.
-- source:
--   AVRAM J-A18 physical signed large-jump interval-additivity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18h_original_largejump_interval_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
      ∫ p in (Ioc s t ×ˢ Iic (-1 : ℝ)), p.2 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
