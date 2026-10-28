-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T18:43:05.399991+00:00
-- url     : https://prove2.me/theorems/45c2af56-ab71-41f7-a256-46f7457ed40b
-- title:
--   Genuine random-terminal Esscher upper-record threshold factorisation with the exact drawdown Laplace reward
-- statement:
--   For every actual spectrally negative Lévy X, genuine Esscher tilted joint random-terminal law Qp, positive exponential rate p, any strict nonnegative upper-record threshold b and positive drawdown transform argument β, the Qp expectation of exp(−β(S_e−X_e)) restricted to the actual event S_e>b is exactly Qp(S_e>b) times the unconditional drawdown Laplace transform. No assumed independence, shifted strong Markov property, arbitrary distributional identity, or generic regeneration hypothesis is placed on the theorem. Prove by combining accepted genuine first-record Qp full-path regeneration with the true measurable limsup drawdown test, actual shifted Lévy pathwise identification, first-record drawdown reset and the atomless clock tie theorem. This is the exact noncircular Wiener–Hopf upper-ray factorisation milestone preceding genuine independence and the finite-rate all-β factor.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.1 WH factorisation (2.4)–(2.7); canonical 4cf7269f conditional first-record Qp regeneration, fc966f64 drawdown normalisation, b626324c strict supremum/first passage, 2876fc1d no clock tie, pending source-faithful shifted Cantor and H∞ rewards.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b β : ℝ) (hb : 0 ≤ b) (hβ : 0 < β) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (ProbabilityTheory.expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
         (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
           (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let S : Ω × ℝ → ℝ := fun z =>
       runningSup X (Real.toNNReal z.2) z.1
     let D : Ω × ℝ → ℝ := fun z =>
       S z - X.X (Real.toNNReal z.2) z.1
     (∫⁻ z in {z : Ω × ℝ | b < S z},
       ENNReal.ofReal (Real.exp (-β * D z)) ∂Qp) =
     Qp {z : Ω × ℝ | b < S z} *
       (∫⁻ z : Ω × ℝ,
         ENNReal.ofReal (Real.exp (-β * D z)) ∂Qp)) := by sorry
