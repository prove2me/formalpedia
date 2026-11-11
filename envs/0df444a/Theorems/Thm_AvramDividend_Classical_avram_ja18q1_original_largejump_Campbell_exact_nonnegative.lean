-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18q1_original_largejump_Campbell_exact_nonnegative
-- name    : AvramDividend.Classical.avram_ja18q1_original_largejump_Campbell_exact_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:05:56.823074+00:00
-- url     : https://prove2.me/theorems/0f9f6693-b600-4dc8-a6d7-45e87b4fbda8
-- title:
--   Original physical negative-large-mark nonnegative Campbell identity
-- statement:
--   For the intrinsic original marked jump measure, the expected nonnegative marked integral of |z| over times (0,t] and marks z≤-1 equals t times the ν integral of |z| on z≤-1. No moment finiteness assumption; extended-real identity, using the already Proved original negative-mark count rate.
-- source:
--   J-A18 Q Campbell parent 10f73728. Use original marked measure and Proved original unit negative-borel mark rates and monotone integration, no auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18q1_original_largejump_Campbell_exact_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ t : ℝ≥0,
      (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
        (t : ℝ≥0∞) *
          (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by sorry
