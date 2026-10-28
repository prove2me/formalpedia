-- Prove2me | solution 1 for intervalIntegral.lintegral_timeTriangle_sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:06:43.352981+00:00
-- url     : https://prove2.me/submissions/2f34d807-54bf-43cb-a0e4-908c04677409

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
open MeasureTheory Set
open scoped ENNReal
open intervalIntegral
noncomputable section
theorem tri1 {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) 
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

theorem tri2 {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) 
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

theorem solution {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter (measurableSet_lt measurable_fst measurable_snd)
  have hF : Measurable (fun p : ℝ × ℝ => ({p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}).indicator (fun z => h (z.1, z.2 - z.1)) p) :=
    (hh.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))).indicator hS
  have e1 := tri1 hh hS hF
  have e2 := tri2 hh hS hF e1
  simp only at e1 e2
  rw [e1, e2, lintegral_lintegral_swap (f := fun t s => ({p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}).indicator (fun z => h (z.1, z.2 - z.1)) (s, t)) (hF.comp measurable_swap).aemeasurable]
  congr 1; ext s
  exact (lintegral_add_left_eq_self (fun t => ({p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}).indicator (fun z => h (z.1, z.2 - z.1)) (s, t)) s).symm
end
