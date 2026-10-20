-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
-- name    : CohnElkies.lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/2f45ff33-4cf0-477e-9b09-972e8a488d66
-- title:
--   CohnElkies.lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
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

theorem CohnElkies.lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ((d : ℝ) / 2)) T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
              (z.re - ((d : ℝ) / 2) * T))
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) -
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (lowerGammaBoundaryCapped
        ((d : ℝ) / 2) R D s)) := by sorry
