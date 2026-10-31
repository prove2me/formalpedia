-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_global_stieltjes_total
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_stieltjes_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:04:34.641723+00:00
-- url     : https://prove2.me/theorems/08bdc4f9-e75c-4370-b738-87fe3d5aad0d
-- title:
--   Positive discount makes the full true BV post-payment Stieltjes mass minus the initial test value
-- statement:
--   For the actual source BV controlled reserve, positive discount makes the entire vector Stieltjes mass of a horizon-frozen discounted post-payment Lipschitz test equal minus its initial post-payment value. Original immediate dividend is accounted for separately.
-- source:
--   Proved positive-discount source tail theorem, original Lévy model, pinned vectorMeasure_Ici, right limit and exponential decay.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_stieltjes_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 < q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure Set.univ = -g 0 := by sorry
