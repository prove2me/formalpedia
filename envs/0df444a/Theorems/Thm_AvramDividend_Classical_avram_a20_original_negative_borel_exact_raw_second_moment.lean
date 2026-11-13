-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_exact_raw_second_moment
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_exact_raw_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:41:23.406107+00:00
-- url     : https://prove2.me/theorems/be01dfb8-b744-4147-84e1-5622f128652b
-- title:
--   True original negative Borel marked jump count has exact raw quadratic moment r²+r
-- statement:
--   For the literal source intrinsic count of arbitrary measurable negative Borel jump marks under finite activity, the real-valued jump count J is square-integrable and E[J²]=r²+r, where r=T ν(B). This follows directly from the authoritative accepted original factorial second moment E[J(J−1)]=r² and original count first moment E[J]=r, using the exact pointwise identity J²=J(J−1)+J, the sum of integrable random variables and linearity of integration. Supplies physical bounded-cell exact raw square moments for weighted-mark approximations and source-Gaussian residual estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_exact_raw_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let J : Ω → ℝ := fun ω => (N ω).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (J ω) ^ 2) P ∧
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r := by sorry
