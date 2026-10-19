-- Prove2me | Theorems.Thm_CohnElkies_harmonic_upper_joint_tendsto_zero
-- name    : CohnElkies.harmonic_upper_joint_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/fd4b3c10-297f-4ba1-9665-756591349731
-- title:
--   CohnElkies.harmonic_upper_joint_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.harmonic_upper_joint_tendsto_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) + Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by sorry
