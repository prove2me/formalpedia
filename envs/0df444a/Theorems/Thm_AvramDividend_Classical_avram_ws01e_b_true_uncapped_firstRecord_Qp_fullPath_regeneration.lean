-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
-- name    : AvramDividend.Classical.avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:56:26.810949+00:00
-- url     : https://prove2.me/theorems/f5788ba0-5ca1-4ac9-ad2a-8c147d4c369c
-- title:
--   Uncapped genuine terminal Esscher upper-record residual-clock and full shifted-path reward factor
-- statement:
--   For an actual spectrally negative Lévy process and genuine random-terminal Esscher path-clock law Qp, the arbitrary nonnegative jointly measurable reward of the residual real exponential clock and entire path shifted after the uncapped first strict upper record has an exact unnormalised factorisation on the source-faithful event first record finite and before or at the real clock. The multiplier is the original-law first-record stopped survival discount integral and the second factor is the independent fresh true-Qp random-terminal whole-path reward marginal. This is obtained by increasing finite-cap regeneration identities and monotone convergence, with no WH factor or tilted strong Markov assertion assumed.
-- source:
--   Use canonical Proved capped whole-path true Qp regeneration 3fe509bd, actual upper passage clock measurability 7ded075d, shifted whole path measurability 8e59a363 and increasing natural finite cap exhaustion. On T_b<n the censored clock equals T_b.toNNReal; both capped reward and capped stopped survival discount are restrictions of fixed measurable uncapped reward densities. Apply measure_iUnion to their withDensity measures and ENNReal.iSup_mul. No division and no all-beta formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
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
     let E : Set (Ω × ℝ) :=
       {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let D : Set Ω := {ω | T ω < ⊤}
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E,
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
       ∂Qp) =
     (∫⁻ ω in D, discount (age ω) ∂P) *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by sorry
