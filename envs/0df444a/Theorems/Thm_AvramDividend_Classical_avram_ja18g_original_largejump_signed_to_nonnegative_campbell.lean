-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_signed_to_nonnegative_campbell
-- name    : AvramDividend.Classical.avram_ja18g_original_largejump_signed_to_nonnegative_campbell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:58:54.945237+00:00
-- url     : https://prove2.me/theorems/379ca63e-2610-47cf-8a40-f78f491f13cf
-- title:
--   Original physical signed largejump-sum expectation equals negative absolute-mark Campbell mass
-- statement:
--   On the original sample space, use negative signs of the actual jump marks and first-moment integrability to identify the signed expected original largejump sum with the negative real value of the exact double ENNReal absolute-mark integral. This is the only physical path-to-measure bridge remaining before signed Campbell mean.
-- source:
--   J-A18 signed Campbell mean bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_largejump_signed_to_nonnegative_campbell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
      - (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P).toReal := by sorry
