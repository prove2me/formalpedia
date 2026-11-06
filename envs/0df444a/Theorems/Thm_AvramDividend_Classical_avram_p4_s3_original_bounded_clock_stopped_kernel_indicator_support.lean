-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_clock_stopped_kernel_indicator_support
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_clock_stopped_kernel_indicator_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:06:08.774638+00:00
-- url     : https://prove2.me/theorems/b1669240-db89-4087-b512-d9466690e5ac
-- title:
--   Bounded original stopped predictable source kernel is supported on its deterministic horizon
-- statement:
--   For a sample-dependent stopped clock τ bounded above by the physical deterministic horizon T, any stopped source kernel G·1_{u≤τ} vanishes outside u≤T. Therefore the deterministic-horizon indicator of that kernel is itself. This exact support equation supplies the hSupport hypothesis for original stopped compensated-source mean-zero theorems, without assumptions on an abstract process law.
-- source:
--   Order inclusion u≤τ(ω)≤T and the defining indicator support identity, matching the support side-condition of the accepted original stopped compensated-source mean-zero theorem f445799e.

import Mathlib
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_clock_stopped_kernel_indicator_support
    {Ω : Type*} (T : ℝ≥0) (τ : Ω → ℝ≥0∞)
    (hτT : ∀ ω, τ ω ≤ (T : ℝ≥0∞))
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : S = {p | p.1.1 ≤ T})
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) :
    S.indicator (fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) =
      (fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) := by sorry
