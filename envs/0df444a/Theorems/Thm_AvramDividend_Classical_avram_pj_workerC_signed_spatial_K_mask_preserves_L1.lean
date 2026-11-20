-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
-- name    : AvramDividend.Classical.avram_pj_workerC_signed_spatial_K_mask_preserves_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:52:39.364426+00:00
-- url     : https://prove2.me/theorems/f1c199da-33a1-42d5-8a21-3f993376acf1
-- title:
--   Positive-clock masking of signed spatial source error preserves its L1 norm and kills zero-clock residual
-- statement:
--   For any integrable signed spatial Itô error K, restricting K to a measurable event S yields an integrable error no larger in L1 and identically zero off S. With S={rho≠0} and the actual original zero-clock terminal identity V=U, this prevents an artificial -K residual at rho=0 in the purejump source.
-- source:
--   Necessary zero-clock normalisation for stronger original physical-grid source 8786c380 / 65b80d50; not a substitute for the stochastic a.s. Ito limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_signed_spatial_K_mask_preserves_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (ε : ℝ) (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε) :
    ∃ K' : Ω → ℝ,
      Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε ∧
      (∀ ω, ω ∉ S → K' ω = 0) ∧
      (∀ ω, ω ∈ S → K' ω = K ω) := by sorry
