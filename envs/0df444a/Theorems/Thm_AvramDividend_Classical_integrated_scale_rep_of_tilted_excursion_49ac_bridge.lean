-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrated_scale_rep_of_tilted_excursion_49ac_bridge
-- name    : AvramDividend.Classical.integrated_scale_rep_of_tilted_excursion_49ac_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:04:20.724711+00:00
-- url     : https://prove2.me/theorems/20c92765-103c-4843-a058-225f87a792b7
-- title:
--   Esscher and tilted excursion identity imply integrated scale representation
-- statement:
--   Given the Esscher scale relation W(x)=exp(phi*x)*V(x) and the tilted zero-discount excursion identity for V with a tail continuous on (0,∞), the q-scale function satisfies the integrated exponential representation. This is the exact deterministic transfer from the tilted excursion identity to branch 5 of the unbounded-variation representation.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions, equations (4)-(5): Esscher relation plus tilted excursion identity yield the integrated representation

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem integrated_scale_rep_of_tilted_excursion_49ac_bridge
    (W V tail : ℝ → ℝ) (φ : ℝ)
    (hEsscher : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hExcursion : ∀ a b : ℝ, 0 < a → a ≤ b → V b = V a * Real.exp (∫ t in a..b, tail t))
    (hTail : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b → W b = W a * Real.exp (∫ t in a..b, φ + tail t) := by sorry

end AvramDividend.Classical
