-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger103_original_bounded_ruinclipped_strict_mass_L1
-- name    : AvramDividend.Classical.avram_gledger103_original_bounded_ruinclipped_strict_mass_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:47:50.924372+00:00
-- url     : https://prove2.me/theorems/a35d66f9-b9d9-4e3e-9d1f-368e75cdff45
-- title:
--   The original bounded ruin-clipped unweighted strict dividend mass is integrable
-- statement:
--   The unweighted original Stieltjes dividend mass strictly before an arbitrary measurable bounded clock is L1 whenever that clock is no later than ruin. It is pointwise bounded by exp(qn) times finite discounted strict original dividend cash, which is integrable. This is the necessary first component of the original Gaussian mesh-error theorem gledger39.
-- source:
--   Original bounded ruin-clipped strict mass integrability needed to assemble gledger39 and gledger81, using gledger98, gledger100, gledger101, gauss13, and original closed-cash finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger103_original_bounded_ruinclipped_strict_mass_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρmeas : Measurable ρ)
    (hρbound : ∀ ω, ρ ω ≤ n)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    Integrable (fun ω : Ω =>
      (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal) P := by sorry
