-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
-- name    : AvramDividend.Classical.avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:56:45.672911+00:00
-- url     : https://prove2.me/theorems/da275876-06bd-4b53-8e60-4a5280bc6bb7
-- title:
--   Original finite negative Borel jump-mark compensated simple gain is integrable with exact zero mean
-- statement:
--   For actual finite-activity spectrally negative Levy jump marks on the original sample space, any finite deterministic real-weighted linear combination of compensated negative Borel-mark counts up to physical time t is integrable and has exactly zero unconditional expectation, without assuming mark-cell disjointness or a global negative-jump second moment.
-- source:
--   Proved original physical negative Borel count first-moment theorem ja35, finite Bochner integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B i)).toReal)
    Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by sorry
