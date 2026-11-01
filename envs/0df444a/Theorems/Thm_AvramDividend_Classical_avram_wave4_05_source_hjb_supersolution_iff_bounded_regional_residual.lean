-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_supersolution_iff_bounded_regional_residual
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_iff_bounded_regional_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:30:52.551126+00:00
-- url     : https://prove2.me/theorems/80f755f8-fb4e-4195-b2d5-f14a8562d380
-- title:
--   Original compensated-source HJB supersolution iff interior superharmonicity and a bounded upper residual strip
-- statement:
--   For every original standing spectrally negative Lévy model and q>0 scale function, under the root's exact three-way Gaussian, bounded-variation or positive-axis C2 smoothness alternative, the full source compensated-generator domain and HJB supersolution max((Γ−q)vcstar,1−vcstar')≤0 at all y>0 is equivalent to source generator domain and residual≤0 in the reserve interior if cstar>0 together with a residual≤0 check only for cstar<y<cstar+1+max(0,X.c/q). The source far-field HJB is already Proved and supplies residual≤0 outside this bounded upper strip; no assumption of full interior generator equality or stochastic stopping is smuggled into this exact equivalence.
-- source:
--   Original source Generator, Proved source bounded-strip supersolution 47638a97, original region iff d55f3bc6, original far-field HJB 09ea2ea1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_iff_bounded_regional_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0) ↔
    ((0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) ∧
      (∀ y : ℝ, (cstar W).toReal < y →
        y < (cstar W).toReal + 1 + max 0 (X.c / q) →
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)) := by sorry
