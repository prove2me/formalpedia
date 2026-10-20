-- Prove2me | Theorems.Thm_CohnElkies_schwartz_imaginaryRiesz_integrable
-- name    : CohnElkies.schwartz_imaginaryRiesz_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/113d0cdf-7452-4bcc-96ba-65259c22ddd4
-- title:
--   CohnElkies.schwartz_imaginaryRiesz_integrable
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

theorem CohnElkies.schwartz_imaginaryRiesz_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    Integrable
      (fun x : Euclidean d =>
        f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by sorry
