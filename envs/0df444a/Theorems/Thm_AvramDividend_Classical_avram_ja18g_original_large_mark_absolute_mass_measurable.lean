-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_mark_absolute_mass_measurable
-- name    : AvramDividend.Classical.avram_ja18g_original_large_mark_absolute_mass_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T03:24:33.449196+00:00
-- url     : https://prove2.me/theorems/fe56464b-8737-4b16-baa2-c4a7f97acadb
-- title:
--   Original large negative marked jump absolute mass is sample measurable
-- statement:
--   For each deterministic t, the original jump measure of the given spectrally negative Lévy process yields a measurable sample-space mapping from ω to its truncated absolute large-negative-jump mark mass. This is the precise measurability premise needed to infer a.e finite mass from the Proved original nonnegative Campbell expectation, and then identify the original signed Bochner sum with the negative Campbell mass.
-- source:
--   J-A18 physical signed Campbell compiler-guided reduction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_large_mark_absolute_mass_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0,
    Measurable (fun ω : Ω =>
      ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
