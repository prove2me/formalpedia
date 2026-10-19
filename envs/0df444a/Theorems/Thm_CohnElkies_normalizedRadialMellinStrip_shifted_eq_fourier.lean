-- Prove2me | Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_shifted_eq_fourier
-- name    : CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/ef00eb6b-137c-4815-83b4-9c762ad391b2
-- title:
--   CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier
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

theorem CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R : ℝ) (hR : 0 < R) (a t : ℝ) :
    normalizedRadialMellinStrip hd f R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) =
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) := by sorry
