-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18q2_original_largejump_pathwise_enorm_bound
-- name    : AvramDividend.Classical.avram_ja18q2_original_largejump_pathwise_enorm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:05:58.048891+00:00
-- url     : https://prove2.me/theorems/78afd1eb-7ad6-4449-9612-a08c9d2d5548
-- title:
--   Pathwise norm of original signed jump integral bounded by absolute marked lintegral
-- statement:
--   For every original sample path and horizon, the enlarged norm of the signed Bochner large-jump integral is bounded by the nonnegative integral of absolute marks over the exact same intrinsic random measure, without integrability assumptions.
-- source:
--   J-A18 Q Campbell parent 10f73728; direct Bochner enorm-integral inequality on the physical random marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18q2_original_largejump_pathwise_enorm_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (t : ℝ≥0) (ω : Ω),
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ≤
        (∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
          ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
