-- Prove2me | solution 1 for intervalIntegral.integral_timeTriangle_sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:11:38.535692+00:00
-- url     : https://prove2.me/submissions/be5916c4-c56e-4baa-ba5a-a1c5ca5413a4

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
open MeasureTheory Set
open scoped ENNReal
open intervalIntegral

theorem solution {h : ℝ × ℝ → ℝ} (hh : Measurable h)
    (hint : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator h)
      (volume.prod volume)) :
    (∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), h (s, u) := by
  set g := (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator h with hg
  have hgm : Measurable g := hh.indicator (measurableSet_Ioi.prod measurableSet_Ioi)
  have hmp := measurePreserving_prod_sub_swap (volume : Measure ℝ) (volume : Measure ℝ)
  have hint2 : Integrable (g ∘ fun z : ℝ × ℝ => (z.2, z.1 - z.2)) (volume.prod volume) :=
    (hmp.integrable_comp hgm.aestronglyMeasurable).2 hint
  -- RHS as a product integral
  have hR : (∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), h (s, u)) =
      ∫ z, g z ∂(volume.prod volume) := by
    rw [integral_prod g hint, ← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; funext s
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs, ← MeasureTheory.integral_indicator measurableSet_Ioi]
      congr 1; funext u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · simp [hg, indicator_of_mem hu, indicator_of_mem (show (s, u) ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) from ⟨hs, hu⟩)]
      · rw [indicator_of_notMem hu, hg, indicator_of_notMem (fun h' => hu h'.2)]
    · rw [indicator_of_notMem hs]
      symm
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [hg, Pi.zero_apply]
      exact indicator_of_notMem (fun h' => hs h'.1) _
  -- LHS as a product integral
  have hL : (∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫ z, (g ∘ fun z : ℝ × ℝ => (z.2, z.1 - z.2)) z ∂(volume.prod volume) := by
    rw [integral_prod _ hint2, ← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, ← MeasureTheory.integral_indicator measurableSet_Ioo]
      congr 1; funext s
      by_cases hs : s ∈ Ioo (0 : ℝ) t
      · have hm : (s, t - s) ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := ⟨hs.1, by simp [hs.2]⟩
        simp [hg, indicator_of_mem hs, indicator_of_mem hm]
      · rw [indicator_of_notMem hs]
        simp only [Function.comp, hg]
        refine (indicator_of_notMem (fun h' => hs ⟨h'.1, ?_⟩) _).symm
        have := h'.2; simp only [mem_Ioi, sub_pos] at this; exact this
    · rw [indicator_of_notMem ht]
      symm
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp, hg, Pi.zero_apply]
      refine indicator_of_notMem (fun h' => ht ?_) _
      have h1 := h'.1; have h2 := h'.2
      simp only [mem_Ioi, sub_pos] at h1 h2 ⊢; linarith
  rw [hL, hR]
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hgm.aestronglyMeasurable)]
  rfl
