-- Prove2me | Theorems.Thm_CohnElkies_horizontalStrip_norm_extension_majorization
-- name    : CohnElkies.horizontalStrip_norm_extension_majorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.667982+00:00
-- url     : https://prove2.me/theorems/81abb850-baa7-41c2-a060-bb785bf89e48
-- title:
--   CohnElkies.horizontalStrip_norm_extension_majorization
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

theorem CohnElkies.horizontalStrip_norm_extension_majorization
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (f : ℂ → ℂ) (N : ℂ → ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.im ⁻¹' Ioo a b))
    (hN : ContinuousOn N
      (Complex.im ⁻¹' Icc a b))
    (hNnonneg : ∀ w : ℂ,
      w.im ∈ Icc a b → 0 ≤ N w)
    (hinterior : ∀ w : ℂ,
      w.im ∈ Ioo a b → N w = ‖f w‖)
    (hbottom : ∀ w : ℂ, w.im = a → N w ≤ C)
    (htop : ∀ w : ℂ, w.im = b → N w ≤ C)
    (hgrowth :
      ∃ c < Real.pi / (b - a), ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap (fun w : ℂ => |w.re|)
              Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹' Ioo a b))
          f
          (fun w : ℂ =>
            Real.exp (B * Real.exp (c * |w.re|))))
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    N z ≤ C := by sorry
