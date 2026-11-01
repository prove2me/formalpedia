-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_controlled_negative_strip_quadratic_budget
-- name    : AvramDividend.Classical.avram_wave4_04_original_controlled_negative_strip_quadratic_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:13:50.111477+00:00
-- url     : https://prove2.me/theorems/246dcd6f-e5ff-4737-a3e2-75f31f5e0f4d
-- title:
--   Uniform original-process controlled quadratic jump energy on every negative truncation strip
-- statement:
--   For the original spectrally negative Levy process X and the same adapted dividend strategy D, the predictable clipped left-limit reserve jump kernel has a uniform quadratic energy estimate over any measurable negative-mark set E. A single constant K chosen from the actual source Lévy measure and the local C1/killed boundary assumptions works for all strips, even when ∫|z| ν(dz) diverges. Combining this with the Proved source small-jump ν-energy tail and original-horizon predictable observation measure supplies the quantitative marked L2 cutoff needed to invoke a future actual-source compensated jump isometry. It neither asserts that source compensated martingales are already defined nor changes the corrected UBV main theorem.
-- source:
--   Avram-Palmowski-Pistorius (2007) Proposition 4(i); exact Proved source full-mark envelope 00ebb997-58eb-47ba-9a38-1e3bf9937d4f, original controlled predictable L2 theorem 18dba881-66b9-4289-a702-c5538ebc5827, original intensity small-jump tail 03134e86-e6de-49ec-8d59-26afc753df00. Corrected original UBV target 429e17ca-5528-40b5-b593-7c03973d0706. No substitution of source X or adapted D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_original_controlled_negative_strip_quadratic_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E : Set ℝ,
      MeasurableSet E → E ⊆ Iio (0 : ℝ) →
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
        μ Set.univ * (ENNReal.ofReal K *
          (∫⁻ z in E, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν)) := by sorry
