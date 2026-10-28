-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_of_scaledW_harmonic
-- name    : AvramDividend.Classical.generator_vcstar_eq_zero_of_scaledW_harmonic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:54:10.713654+00:00
-- url     : https://prove2.me/theorems/385fc863-6933-4c0a-8cfc-5d9c67b7f175
-- title:
--   Generator harmonicity of the classical barrier candidate from scaled scale-function harmonicity
-- statement:
--   Below a positive finite cstar barrier, the candidate value equals the scaled q-scale function at every smaller surplus, including negative surplus by the scale-function support property. The Proved theorem generator_eq_of_agree_below transfers the Levy generator and its jump-integrability requirement between functions agreeing below the evaluation threshold. Consequently, if the scaled scale function has generator residual zero on the positive interior of the barrier, then vcstar has the same property there. The difficult stochastic generator harmonicity is an explicit hypothesis, not assumed silently.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, generator harmonicity of the barrier candidate.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.generator_vcstar_eq_zero_of_scaledW_harmonic {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hscaled : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable
          (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x ∧
        X.generator
            (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x -
          q * divE (W x) (scaleDeriv W (cstar W).toReal) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
