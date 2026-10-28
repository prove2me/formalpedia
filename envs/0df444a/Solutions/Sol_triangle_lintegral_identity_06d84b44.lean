-- Prove2me | solution 1 for triangle_lintegral_identity_06d84b44
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:04:48.730297+00:00
-- url     : https://prove2.me/submissions/a8035d6b-c386-4f47-814f-97039a406c7b

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
    : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t)) := by
  intro S F
  have inner : ∀ t : ℝ, ∫⁻ s, F (s, t) = (Ioi (0:ℝ)).indicator (fun t => ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) t := by
    intro t
    have e : (fun s => F (s, t)) = (Ioo (0:ℝ) t).indicator (fun s => h (s, t - s)) := by
      ext s
      simp only [F, S, Set.indicator, Set.mem_setOf_eq, Set.mem_Ioo]
    rw [e, lintegral_indicator measurableSet_Ioo]
    by_cases ht : 0 < t
    · simp [Set.indicator, ht]
    · have : Ioo (0:ℝ) t = ∅ := Set.Ioo_eq_empty (by simpa using ht)
      simp [Set.indicator, ht, this]
  simp_rw [inner]
  rw [lintegral_indicator measurableSet_Ioi]
end
