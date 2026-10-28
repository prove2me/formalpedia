-- Prove2me | solution 1 for triangle_lintegral_identity_b176d7f6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:05:04.742363+00:00
-- url     : https://prove2.me/submissions/5f6c7772-c433-4dbd-b5d0-051693b256c0

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
open MeasureTheory Set
open scoped ENNReal
open intervalIntegral
noncomputable section
theorem solution {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) 
    (hS : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; MeasurableSet S))
    (hF : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; Measurable F))
    (hleft : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t)))
    : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u)) =
      ∫⁻ s, ∫⁻ u, F (s, s + u)) := by
  intro S F
  have inner : ∀ s : ℝ, ∫⁻ u, F (s, s + u) = (Ioi (0:ℝ)).indicator (fun s => ∫⁻ u in Ioi (0 : ℝ), h (s, u)) s := by
    intro s
    by_cases hs : 0 < s
    · have e : (fun u => F (s, s + u)) = (Ioi (0:ℝ)).indicator (fun u => h (s, u)) := by
        ext u
        simp only [F, S, Set.indicator, Set.mem_setOf_eq, Set.mem_Ioi, hs, true_and,
          lt_add_iff_pos_right, add_sub_cancel_left]
      rw [e, lintegral_indicator measurableSet_Ioi]
      simp [Set.indicator, hs]
    · have e : (fun u => F (s, s + u)) = fun _ => 0 := by
        ext u
        simp [F, S, Set.indicator, hs]
      rw [e]
      simp [Set.indicator, hs]
  simp_rw [inner]
  rw [lintegral_indicator measurableSet_Ioi]
end
