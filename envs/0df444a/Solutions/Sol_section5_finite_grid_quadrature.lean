-- Prove2me | solution 1 for section5_finite_grid_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:24.092015+00:00
-- url     : https://prove2.me/submissions/a732446c-6850-4b2e-ad28-9183f1f97790

import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5FiniteGridMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
theorem solution (n N : ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    (∫ x, F (fun i => section5_grid_sample a δ (x i))
      ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ))))) =
      (δ^n : ℂ) * ∑ j : Fin n → Fin N, F (fun i => a+(j i:ℝ)*δ) := by
  have hmap := integral_map
    (μ := Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ))))
    (f := F) (φ := fun x : Fin n → ℝ => fun i => section5_grid_sample a δ (x i))
    (measurable_pi_lambda _ (fun i =>
      (section5_grid_sample_measurable a δ).comp (measurable_pi_apply i))).aemeasurable
    hF.aestronglyMeasurable
  rw [← hmap,section5_grid_sample_map_pi n N a δ hδ,
    integral_map (measurable_of_countable _).aemeasurable hF.aestronglyMeasurable,
    integral_smul_measure,integral_count]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_ofReal hδ.le,Complex.real_smul,Complex.ofReal_pow]
