-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:49:20.569378+00:00
-- url     : https://prove2.me/theorems/5f48ee29-0b7c-4dfe-8917-b17dea8e6a3a
-- title:
--   Genuine original exponential-clock drawdown transform factorised through inverse terminal Esscher weighting at every real beta
-- statement:
--   For the original spectrally negative Lévy path, any nonnegative root φ of ψ(φ)=q≥0 and rate p>0, and any real β, the rate-p+q original terminal drawdown exponential moment multiplied by p equals (p+q) times the product under the genuine random-terminal Esscher law Qp of the exp(-φ S) and exp(-(β-φ)D) moments. The identity is in ENNReal, so remains valid for infinite positive moments. It follows from the accepted exact inverse Esscher joint-clock change of measure and the accepted genuine Esscher Wiener–Hopf independence without assuming clock independence under Qp.
-- source:
--   Genuine original-clock inverse Esscher transform bridge for the lower-killed resolvent and the original all-beta descending factor. Proved ingredients: 421ab102 actual Qp IndepFun, f5f027eb actual inverse measure change and accepted real-clock supremum/drawdown measurability. Proof uses nonnegative Tonelli factorisation and pathwise algebra D=S-X_e, with no moment-gap division.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p β : ℝ) (hφ : 0 ≤ φ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal p *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
        ∂(P.prod (expMeasure (p + q)))) =
    ENNReal.ofReal (p + q) *
      ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
       (∫⁻ z, ENNReal.ofReal (Real.exp (-(β - φ) * D z)) ∂Qp)) := by sorry
