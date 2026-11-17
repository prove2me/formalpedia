-- Prove2me | solution 1 for thm_6_7_complex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:28:09.652137+00:00
-- url     : https://prove2.me/submissions/4672f80d-6e27-4aaf-b5ab-87ab57e68184

import Theorems.Thm_complexTextbookIntegrable_iff_integrable
import Theorems.Thm_Thm67Support_complexTextbookIntegral_eq_some_integral
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic


/-! # Theorem 6.7: linearity of the Lebesgue integral -/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace Thm67Support

end Thm67Support

/-
For a measurable complex-valued function, textbook integrability of its
real and imaginary parts is equivalent to Bochner integrability.
-/


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by
  refine' ⟨ _, _, _, _ ⟩;
  · convert complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => Z ω + W ω from hZm.add hWm ) |>.2 ( Integrable.add ( complexTextbookIntegrable_iff_integrable hZm |>.1 hZ ) ( complexTextbookIntegrable_iff_integrable hWm |>.1 hW ) ) using 1;
  · have hZi : Integrable Z μ := (complexTextbookIntegrable_iff_integrable hZm).1 hZ
    have hWi : Integrable W μ := (complexTextbookIntegrable_iff_integrable hWm).1 hW
    have hsum : Integrable (fun ω => Z ω + W ω) μ := hZi.add hWi
    change complexTextbookIntegral μ (Z + W) = _
    rw [Thm67Support.complexTextbookIntegral_eq_some_integral (hZm.add hWm) hsum,
      Thm67Support.complexTextbookIntegral_eq_some_integral hZm hZi,
      Thm67Support.complexTextbookIntegral_eq_some_integral hWm hWi]
    simp [MeasureTheory.integral_add hZi hWi]
  · convert ( complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => α * Z ω from measurable_const.mul hZm ) ) |>.2 ( MeasureTheory.Integrable.const_mul ( show MeasureTheory.Integrable Z μ from ?_ ) α ) using 1;
    exact complexTextbookIntegrable_iff_integrable hZm |>.1 hZ;
  · -- By definition of complexTextbookIntegral, we know that
    have h_integrable : Integrable (fun ω => α * Z ω) μ := by
      exact MeasureTheory.Integrable.const_mul ( by simpa using ( complexTextbookIntegrable_iff_integrable hZm ).mp hZ ) α;
    rw [ Thm67Support.complexTextbookIntegral_eq_some_integral, Thm67Support.complexTextbookIntegral_eq_some_integral ];
    · simp [ MeasureTheory.integral_const_mul ];
    · exact hZm;
    · exact (complexTextbookIntegrable_iff_integrable hZm).mp hZ;
    · exact measurable_const.mul hZm;
    · exact h_integrable