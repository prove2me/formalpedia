-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:08:05.393407+00:00
-- url     : https://prove2.me/theorems/f94acce4-00f4-4e2b-8403-d2e7390c0b89
-- title:
--   Original-clock descending drawdown Laplace integral equals the real MGF on positive parameters
-- statement:
--   For any genuine original spectrally negative Lévy law and independent Exp(p) clock, with p>0 and β>0, the ENNReal Laplace integral of the actual terminal drawdown D=S_e−X_e equals ENNReal.ofReal of the real MGF of −D at β. This specialises the already accepted general genuine Esscher-clock identity to θ=0, uses ψ(0)=0, and identifies the density-one original product measure, without assuming a factorisation or finite moments.

import Mathlib.Probability.Moments.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal
      (mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        (P.prod (expMeasure p)) β) := by sorry
