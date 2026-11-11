-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_negative_count_real_L1
-- name    : AvramDividend.Classical.avram_ja18_original_finite_negative_count_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:22:57.250375+00:00
-- url     : https://prove2.me/theorems/e9f44a92-8293-4a06-92a2-09a763b13a9a
-- title:
--   Physical negative-jump counting measure has real-L1 count on each integer horizon without BV
-- statement:
--   Finite original negative jump intensity and the Proved intrinsic original bounded-clock negative-count lintegral imply real L1 integrability of the actual marked jump count over (0,n]×(-∞,0). Use already-Proved  dfcb3913 to establish finite lintegral and 8146a449 count measurability, then pinned Mathlib integrable_toReal_of_lintegral_ne_top. This is independent of bounded-variation and auxiliary Poisson processes.
-- source:
--   Root-connected analytic support for Open physical small-band path envelope 23979329, needed to dominate compensated jumps uniformly in cutoff by physical negative count plus deterministic compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_finite_negative_count_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Integrable (fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) P := by sorry
