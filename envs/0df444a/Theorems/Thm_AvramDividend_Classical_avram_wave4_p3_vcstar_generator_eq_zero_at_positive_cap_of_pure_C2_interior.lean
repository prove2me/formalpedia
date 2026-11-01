-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:08:11.039286+00:00
-- url     : https://prove2.me/theorems/7f85ba1f-e72c-42b4-b922-9058793b0a19
-- title:
--   Pure-jump C² positive optimal-barrier generator equality from explicitly assumed strict-interior harmonicity
-- statement:
--   For the actual capped dividend candidate of a spectrally negative Lévy process with σ=0 and infinite variation, global positive-reserve C² regularity and a genuine interior generator residual identity on (0,c*) imply the integrable zero generator residual at exactly the positive cap c*. The proof uses the already proved noncircular compensated generator continuity at the cap, an actual left-neighborhood limit, and the proved C² generator-domain theorem. It does not prove or postulate interior harmonicity as a fact; this is an explicit assumption suitable for Chat05's future canonical provider.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4 only on open (0,c*) plus strict endpoint continuity. Proved P3 pure C² residual continuity a979ad51-e582-4380-8bfd-712badb396ae and 05A C² endpoint domain fbf83acf-1bfd-45ee-8c96-930992cc1901; P3 primary target 91803827.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped Topology NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
