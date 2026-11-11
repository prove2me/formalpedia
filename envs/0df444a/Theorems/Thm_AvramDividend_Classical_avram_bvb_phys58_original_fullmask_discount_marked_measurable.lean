-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys58_original_fullmask_discount_marked_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys58_original_fullmask_discount_marked_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:37:58.663241+00:00
-- url     : https://prove2.me/theorems/35f1fb19-ebdc-4126-ba6a-6454546fb76b
-- title:
--   Original predictable full-mask discounted mark factor measurability
-- statement:
--   The finite-cap stopped predictable mask and exponential time discount produce a jointly measurable marked discount factor, with zero outside the mask and for nonnegative marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys58_original_fullmask_discount_marked_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
           (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
           0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) else 0) := by sorry
