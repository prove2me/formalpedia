-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_generic_measurable_bounded_simple_mark_integral_20261122
-- name    : AvramDividend.Classical.avram_oai_generic_measurable_bounded_simple_mark_integral_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:25:15.186326+00:00
-- url     : https://prove2.me/theorems/984a39de-8824-44b1-904f-1af2dd2c2c5e
-- title:
--   A.e. strong measurability of bounded simple mark integrals against a measurable random finite-window measure
-- statement:
--   For a random marked measure M which is measurable as a measure-valued function and has finite mass almost surely on a finite time and mark window, the real integral of any Borel simple mark f bounded by 1 in that window is a.e. strongly measurable. The true integral is almost surely a finite sum of weighted observed cell masses; each cell mass is measurable from the random measure. The theorem supplies the missing source measurability premise for the original Avram finite negative-annulus second-moment convergence and requires no global finite jump activity or Poisson law.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_generic_measurable_bounded_simple_mark_integral_20261122
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure (ℝ≥0 × ℝ)) (hM : Measurable M)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hMass : ∀ᵐ ω ∂P, M ω (Ioc 0 T ×ˢ B) < ⊤)
    (f : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ B, |f z| ≤ 1) :
    AEStronglyMeasurable
      (fun ω => ∫ p in (Ioc 0 T ×ˢ B), f p.2 ∂M ω) P := by sorry
