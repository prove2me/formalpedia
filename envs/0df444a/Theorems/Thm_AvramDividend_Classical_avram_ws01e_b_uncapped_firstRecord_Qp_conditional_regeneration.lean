-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
-- name    : AvramDividend.Classical.avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:19:08.184242+00:00
-- url     : https://prove2.me/theorems/4cf7269f-2479-43da-9d75-ab22ce6f7c26
-- title:
--   Actual random-terminal Esscher conditional first-record full-path regeneration with correct event normalisation
-- statement:
--   For the actual spectrally negative Lévy X under probability P, θ≥0 and genuine independent real Exp(p) clock with p>0, the random-terminal Esscher joint law Qp=(P⊗Exp(p)).withDensity(exp(θX_e-eψθ)) has a correctly normalised stopped upper-record renewal identity: the integral of any jointly product-Pi measurable nonnegative test H of the residual real clock and entire centred post-record path, restricted to finite T_b≤e, equals the actual tilted event probability Qp(T_b<∞,T_b≤e) multiplied by the genuine fresh real-clock path likelihood integral. No artificial independence of tilted clock and tilted path is assumed. Its normaliser follows noncircularly by applying the Proved uncapped regeneration theorem to the constant-one test and using unit finite-horizon Esscher mass at every real clock time; valid for every b≥0, θ≥0, p>0. This is the substantive normalised full-path record regeneration needed for tilted Wiener–Hopf independence, leaving the Pi-measurable drawdown approximation and reversal as subsequent steps.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), §2.1, Wiener–Hopf regeneration and exponential records; exact full-path uncapped random-terminal tilted record factor f5788ba0-5ca1-4ac9-ad2a-8c147d4c369c; genuine finite-horizon Esscher probability 6c6f7684-1d83-4271-ac6d-3e584327e2e4. Publication technical repair: the failed first authoring job ee8b9f57 timed out in the five-second import parser while preamble imported two long Proved theorem files. This revised preamble retains the required definition only; the Lean proof source itself imports those theorem files.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E,
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
       ∂Qp) =
     Qp E *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by sorry
