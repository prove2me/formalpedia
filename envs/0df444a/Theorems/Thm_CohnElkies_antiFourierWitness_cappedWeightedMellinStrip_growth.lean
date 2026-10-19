-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_cappedWeightedMellinStrip_growth
-- name    : CohnElkies.antiFourierWitness_cappedWeightedMellinStrip_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/8ee101b9-bfc8-4435-aeea-8756c9b1b77d
-- title:
--   CohnElkies.antiFourierWitness_cappedWeightedMellinStrip_growth
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

theorem CohnElkies.antiFourierWitness_cappedWeightedMellinStrip_growth
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ) :
    ∃ c < Real.pi /
        (((d : ℝ) / 2) - (-((d : ℝ) / 2))),
      ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap
              (fun z : ℂ => |z.re|) Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹'
                Ioo (-((d : ℝ) / 2))
                    ((d : ℝ) / 2)))
          (fun z : ℂ =>
            Complex.exp
                (-(lowerStripCappedGammaOuter
                  ((d : ℝ) / 2) R D z)) *
              normalizedRadialMellinStrip
                hd w.function R z)
          (fun z : ℂ =>
            Real.exp
              (B * Real.exp (c * |z.re|))) := by sorry
