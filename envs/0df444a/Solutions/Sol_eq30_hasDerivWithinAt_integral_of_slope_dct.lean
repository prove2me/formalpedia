-- Prove2me | solution 1 for eq30_hasDerivWithinAt_integral_of_slope_dct
-- status  : ACCEPTED   (disprove)
-- author  : @Secousses
-- created : 2026-11-23T23:52:07.611157+00:00
-- url     : https://prove2.me/submissions/d1968af4-3d12-4dd3-8142-acaf8d9f2608

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (D : Ω → ℝ)
    (B s : ℝ)
    (hG : ∀ t, G t = ∫ ω, F t ω ∂P)
    (hSlopeInt : ∀ t, s ≤ t →
      Integrable (fun ω => slope (fun u => F u ω) s t) P)
    (hSlopeBound : ∀ t, s ≤ t → ∀ ω,
      ‖slope (fun u => F u ω) s t‖ ≤ B)
    (hDeriv : ∀ ω, HasDerivWithinAt (fun t => F t ω) (D ω)
      (Set.Ici s) s)
    (hB : Integrable (fun _ : Ω => B) P),
    HasDerivWithinAt G (∫ ω, D ω ∂P) (Set.Ici s) s) := by
  intro h
  -- P = Lebesgue measure on (0,1], φ x = x⁻¹ is not integrable there.
  set P : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hP
  have : IsFiniteMeasure P := by
    rw [hP]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hφ : ¬ Integrable (fun x : ℝ => x⁻¹) P := by
    intro hi
    have : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hi
    rw [intervalIntegrable_inv_iff] at this
    rcases this with h01 | h01
    · exact zero_ne_one h01
    · exact h01 (Set.left_mem_uIcc)
  have hF : ∀ t : ℝ, ∫ x, (x⁻¹ + t) ∂P = 0 := by
    intro t
    apply integral_undef
    intro hi
    apply hφ
    have := hi.sub (integrable_const t)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hslope : ∀ t : ℝ, ∀ x : ℝ, slope (fun u => x⁻¹ + u) 0 t = t⁻¹ * t := by
    intro t x
    simp [slope_def_field, div_eq_inv_mul]
  have key := @h ℝ _ P (fun t x => x⁻¹ + t) (fun _ => 0) (fun _ => 1) 1 0
    (fun t => (hF t).symm)
    (fun t _ => by simp only [hslope]; exact integrable_const _)
    (fun t _ x => by
      rw [hslope]
      by_cases ht : t = 0
      · simp [ht]
      · simp [inv_mul_cancel₀ ht])
    (fun x => ((hasDerivAt_id (0:ℝ)).const_add x⁻¹).hasDerivWithinAt)
    (integrable_const _)
  have h0 : HasDerivWithinAt (fun _ : ℝ => (0:ℝ)) 0 (Set.Ici 0) 0 :=
    hasDerivWithinAt_const _ _ _
  have huniq := (uniqueDiffOn_Ici (0:ℝ) 0 Set.self_mem_Ici).eq_deriv _ key h0
  rw [integral_const, smul_eq_mul, mul_one, hP] at huniq
  simp at huniq
end
