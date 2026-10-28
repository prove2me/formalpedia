-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T20:16:29.440672+00:00
-- url     : https://prove2.me/theorems/421ab102-88ae-410a-894e-357198318f45
-- title:
--   True finite-rate random-terminal Esscher Wiener–Hopf independence of supremum and terminal drawdown
-- statement:
--   For the actual spectrally negative Lévy process X, probability path law P, positive independent exponential clock of rate p, and the genuine joint random-terminal Esscher law Qp with density exp(theta X_e − e psi(theta)), the true finite-horizon running supremum S_e and terminal drawdown D_e=S_e−X_e are independent random variables under Qp, for every theta≥0 and p>0. This is stronger than a single positive-Laplace threshold factor and is the precise finite-rate Wiener–Hopf independence identity. It is to be established without assuming any independent Qp factor or transferring P independence through an unfactored density, using the already Proved normalised first-record Qp full-path regeneration, arbitrary measurable indicator tests of the full-Pi limsup reward, the true shifted drawdown identity and upper-ray π-λ independence theorem.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.1 factorisation (2.4); proved Qp regeneration 4cf7269f, first record normalisation fc966f64, generic upper-ray IndepFun 92d90ca8, full-Pi drawdown limsup and shifted path identities in corrected publication wave.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ProbabilityTheory.IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) := by sorry
