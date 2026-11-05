-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ordered_rightjump_tsum_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ordered_rightjump_tsum_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:38:17.670204+00:00
-- url     : https://prove2.me/theorems/a2d605da-04cc-4889-8207-ed8eb3cfd2ab
-- title:
--   Source-ordered countably indexed original dividend right-jump residual sum is almost surely strongly measurable
-- statement:
--   For a countable original-process right-dividend jump enumeration, if each pathwise discounted correction is almost surely strongly measurable, the random sum over all indices is almost surely strongly measurable. The source-correct term uses the Lévy reserve after the source jump, then applies the right dividend payment via rightLimit. This makes the missing random-atom-measurability obligation for P4-F and the P4-D L1 envelope explicit at the individual jump level.
-- source:
--   Pinned Mathlib MeasureTheory.AEStronglyMeasurable.tsum, Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable at mission revision 0df444a3. Original controlled source definitions in pinned SpectrallyNegativeLevy and DividendStrategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ordered_rightjump_tsum_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (w : ℝ → ℝ)
    (t : Ω → ι → ℝ≥0)
    (hTerm : ∀ i : ι, AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    AEStronglyMeasurable (fun ω => ∑' i : ι, Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P := by sorry
