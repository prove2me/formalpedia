-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_interval_representation_transfer
-- name    : AvramDividend.Classical.esscher_interval_representation_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:45:56.859021+00:00
-- url     : https://prove2.me/theorems/5a309779-446b-4f62-abb7-7ff5fa9dea14
-- title:
--   Transfer a tilted excursion integral identity to the original q-scale function
-- statement:
--   Under a positive-axis Esscher scaling relation W(x)=exp(phi*x)*V(x), a continuous excursion tail, and the integrated excursion-height formula for V on positive intervals, deduce the corresponding exponential interval formula for W. This isolates the deterministic integral and exponential algebra from probabilistic change-of-measure construction.
-- source:
--   Chan, Kyprianou, Savov (2011), equations (3)-(5), Esscher identity and integrated excursion representation.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.esscher_interval_representation_transfer
    (W V : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (htilt : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)) := by sorry
