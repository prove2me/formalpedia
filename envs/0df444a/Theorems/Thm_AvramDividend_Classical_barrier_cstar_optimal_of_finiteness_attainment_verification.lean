-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_optimal_of_finiteness_attainment_verification
-- name    : AvramDividend.Classical.barrier_cstar_optimal_of_finiteness_attainment_verification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:09:33.826218+00:00
-- url     : https://prove2.me/theorems/b032659b-012d-47e2-9aa5-d800f70e91d1
-- title:
--   Classical barrier cstar optimality from finite cstar, attained policy value and verification bounds
-- statement:
--   The candidate barrier is finite, admissible under the cap and attains the proposed dividend value. The capped value upper bound and the Proved capped supremum-sandwich lemma give optimality under the cap. Under the additional far-field generator inequality, the unrestricted upper bound and the Proved unrestricted supremum-sandwich lemma give global optimality. Capped admissibility implies unrestricted admissibility. The conclusion is precisely the classical optimal-barrier theorem under these three component hypotheses.
-- source:
--   Avram, Palmowski and Pistorius (2007), Optimal Dividend Problem I, final assembly of Theorem 2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_eq_of_attainment_and_upper_bound
import Theorems.Thm_AvramDividend_Classical_valueFunction_eq_of_attainment_and_upper_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_cstar_optimal_of_finiteness_attainment_verification {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hc : cstar W < ⊤)
    (hattain : ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x))
    (hverify : (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x))) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by sorry
