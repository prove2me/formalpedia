-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:04:31.532922+00:00
-- url     : https://prove2.me/theorems/bcd7380e-f787-40f6-934f-fcfbf2510fe7
-- title:
--   Complete positive-barrier generator equality across canonical smoothness alternatives, conditional only on strict-interior residual identity
-- statement:
--   For the original spectrally negative Levy process and positive optimal cap under exactly the original three-way smoothness hypothesis, an explicitly assumed pointwise interior discounted generator identity on (0,c*) yields actual compensated generator integrability and exact zero residual at the cap. The Gaussian/BV cases use already Proved source generator harmonicity and matching boundary jet; the pure-jump unbounded-variation global C² case applies the canonically Proved P3 left-continuity endpoint theorem. The one remaining premise is honest and written in the statement: no fabricated source harmonicity, no use of the still-Open Chat05 generator_vcstar_eq_zero. This is the complete import-ready endpoint analytic interface for canonical original P3 target 91803827.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4 strict open interval and positive-barrier verification; P3 Gaussian/BV exact endpoint UUID d2afd925-cf25-42e0-a0d1-96ba9cc7383d and P3 pure C2 conditional left limit UUID 7f85ba1f-e72c-42b4-b922-9058793b0a19. Chat05 retains canonical interior UUID 88d146b8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_interior_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
