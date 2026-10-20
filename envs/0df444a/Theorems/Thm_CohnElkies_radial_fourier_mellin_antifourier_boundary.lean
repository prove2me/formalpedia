-- Prove2me | Theorems.Thm_CohnElkies_radial_fourier_mellin_antifourier_boundary
-- name    : CohnElkies.radial_fourier_mellin_antifourier_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/da5729b0-54e1-410b-b2fd-0f3ab6292184
-- title:
--   CohnElkies.radial_fourier_mellin_antifourier_boundary
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

theorem CohnElkies.radial_fourier_mellin_antifourier_boundary {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (y : ℝ) (hy : y ≠ 0) :
    Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2) *
        mellin (radialProfile hd f) (-(Complex.I * (y : ℂ))) =
      -((Real.pi : ℂ) ^
          (((d : ℂ) / 2) + Complex.I * (y : ℂ)) *
        Complex.Gamma (-(Complex.I * (y : ℂ)) / 2) *
        mellin (radialProfile hd f)
          ((d : ℂ) + Complex.I * (y : ℂ))) := by sorry
