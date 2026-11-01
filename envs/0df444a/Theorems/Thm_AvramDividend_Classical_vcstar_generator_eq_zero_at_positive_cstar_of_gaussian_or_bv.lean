-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
-- name    : AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:04:07.558245+00:00
-- url     : https://prove2.me/theorems/d2afd925-cf25-42e0-a0d1-96ba9cc7383d
-- title:
--   Positive optimal barrier generator equality for Gaussian or bounded-variation source Levy processes
-- statement:
--   For the original spectrally negative Levy process, the positive optimal dividend barrier is in the domain of the original compensated generator, with exactly zero discounted generator residual, under either strictly positive Gaussian coefficient or bounded-variation paths. This authentic two-case endpoint theorem follows by original-process source scale q-harmonicity at every positive reserve, scaling by the nonzero optimal normaliser, and matching the original barrier candidate's values, first derivative and Gaussian-weighted second derivative at the cap. It omits the unresolved pure-jump infinite-variation global C2 case and requires no above-barrier generator assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5, Lemma 4, positive-barrier smooth fit and source generator. Parent AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar 91803827-9c02-4911-969e-c81c0bfc4afc. Uses Proved Gaussian source scale generator harmonicity c352e6e5 and Proved BV source generator harmonicity 711ca87b, plus matching weighted-jet 22df0d92 and generator locality 89017564. Remaining parent branch: sigma=0, unbounded variation and C2 dividend candidate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar_of_gaussian_or_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (halt : 0 < X.σ ∨ X.BoundedVariation) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
