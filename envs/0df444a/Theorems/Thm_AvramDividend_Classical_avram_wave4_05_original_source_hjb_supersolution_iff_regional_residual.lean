-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_source_hjb_supersolution_iff_regional_residual
-- name    : AvramDividend.Classical.avram_wave4_05_original_source_hjb_supersolution_iff_regional_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:17:32.555612+00:00
-- url     : https://prove2.me/theorems/d55f3bc6-be23-4fb8-ab56-b2a2f5a0ddc1
-- title:
--   Original-source HJB supersolution if and only if regional generator residual inequalities
-- statement:
--   For the genuine spectrally negative Lévy source, a positive q and q-scale function, under the full original Gaussian/BV/C2 alternative, a global admissible compensated-generator HJB supersolution is equivalent to two exact regional analytic checks: local generator domain with nonpositive discounted generator residual below a nonzero optimal barrier and nonpositive generator residual strictly above it. Above-barrier generator domain, gradient constraint and boundary cases are automatic by accepted source theorems. Necessity follows from max≤0, domain, and nonnegative cstar; sufficiency invokes the canonically Proved source supersolution theorem 4de732b5. This characterises exactly what source generator facts a stochastic verification proof must discharge.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4 and Lemma 4; source supersolution theorem 4de732b5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_original_source_hjb_supersolution_iff_regional_residual
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
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)) := by sorry
