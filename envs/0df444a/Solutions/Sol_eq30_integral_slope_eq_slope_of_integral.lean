-- Prove2me | solution 1 for eq30_integral_slope_eq_slope_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:46:44.710314+00:00
-- url     : https://prove2.me/submissions/934280ad-0aba-4785-a0ae-9dc6d9f24d20

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (s t : ℝ)
    (hG : ∀ u, G u = ∫ ω, F u ω ∂P)
    (hFs : Integrable (F s) P) (hFt : Integrable (F t) P) :
    (∫ ω, slope (fun u => F u ω) s t ∂P) = slope G s t := by
  by_cases hst : s = t
  · subst t
    simp
  · simp only [slope_def_field, div_eq_mul_inv]
    rw [show (fun ω => (F t ω - F s ω) * (t - s)⁻¹) =
        (fun ω => (t - s)⁻¹ * (F t ω - F s ω)) by
      funext ω
      ring]
    rw [integral_const_mul, integral_sub hFt hFs, ← hG t, ← hG s]
    ring
end
