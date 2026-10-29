-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_Qp_weighted_supremum_single_test_factor
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_Qp_weighted_supremum_single_test_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:09:26.488343+00:00
-- url     : https://prove2.me/theorems/12028505-046f-423b-801c-78a1e042b780
-- title:
--   Genuine tilted exponential-clock one-test Wiener–Hopf exponential-moment factor from upper rays
-- statement:
--   For the authentic Esscher-tilted joint exponential-clock law of the spectrally negative Lévy process, the weighted supremum moment with weight exp(-β terminal drawdown) factors as the product of its supremum and descending Laplace moments, at each β>0. Prove from the genuine threshold identity for nonnegative cutoffs, the actual exponential supremum pushforward law, single-test upper-ray extension and layer-cake. No full IndepFun is assumed; no invalid high-rate terminal moment division is used.
-- source:
--   Accepted true Qp upper-record threshold factor, accepted genuine shifted exponential supremum law, and source-faithful layer-cake single-test generic helpers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_Qp_weighted_supremum_single_test_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p lam β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p) (hβ : 0 < β)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (let μ : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal
           (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
     let S : Ω × ℝ → ℝ :=
       fun z => runningSup X (Real.toNNReal z.2) z.1
     let D : Ω × ℝ → ℝ :=
       fun z => S z - X.X (Real.toNNReal z.2) z.1
     (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) *
         ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
       (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) *
         (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ)) := by sorry
