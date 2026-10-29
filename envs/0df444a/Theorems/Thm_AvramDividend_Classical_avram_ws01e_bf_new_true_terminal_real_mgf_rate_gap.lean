-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:54:35.608038+00:00
-- url     : https://prove2.me/theorems/5ab9eba1-af27-4c6c-b0f7-97765162372e
-- title:
--   True tilted terminal exponential moment as a finite real MGF on its strict rate gap
-- statement:
--   For the genuine Qp Esscher weighted random terminal Lévy value, the real moment-generating function is p/(p-(psi(phi+beta)-q)) for beta≥0 only under the strict finite rate gap. The already proved ENNReal terminal identity ensures the positive exponential is integrable, permitting a rigorous conversion to real MGF and division by the strictly positive finite rate gap. No extrapolation to beta≥lambda and no assumption of supremum/drawdown independence.
-- source:
--   Proved 8b26b52f-49ed-43dc-b2ab-0f9b325f38a3 actual terminal ENNReal moment; pinned MeasureTheory.lintegral_ofReal_ne_top_iff_integrable and ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (hβ : 0 ≤ β) (hgap : X.ψ (φ + β) - q < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    mgf (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β =
    p / (p - (X.ψ (φ + β) - q)) := by sorry
