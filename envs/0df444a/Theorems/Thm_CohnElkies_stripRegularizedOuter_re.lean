-- Prove2me | Theorems.Thm_CohnElkies_stripRegularizedOuter_re
-- name    : CohnElkies.stripRegularizedOuter_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/4f92168b-fd58-4902-875f-16fa508b7e04
-- title:
--   CohnElkies.stripRegularizedOuter_re
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

theorem CohnElkies.stripRegularizedOuter_re
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (s : ℝ) (b : ℝ → ℝ)
    (houter : Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ))) :
    (stripRegularizedOuter ℓ b
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) := by sorry
