-- Prove2me | Theorems.Thm_CohnElkies_radial_fourier_mellin_regularized_closed
-- name    : CohnElkies.radial_fourier_mellin_regularized_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/d2d28e7e-d786-46e7-82a7-27de57305558
-- title:
--   CohnElkies.radial_fourier_mellin_regularized_closed
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
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.radial_fourier_mellin_regularized_closed {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hhatZero : (𝓕 f : TestFunction d) (0 : Euclidean d) = 0)
    (s : ℂ) (hs : 0 ≤ s.re) (hsd : s.re ≤ (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s *
        (Complex.Gamma (s / 2))⁻¹ =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        (mellin (radialProfile hd f) ((d : ℂ) - s) *
          (Complex.Gamma (((d : ℂ) - s) / 2))⁻¹) := by sorry
