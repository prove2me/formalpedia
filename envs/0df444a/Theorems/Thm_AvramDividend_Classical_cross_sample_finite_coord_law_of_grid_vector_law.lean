-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_sample_finite_coord_law_of_grid_vector_law
-- name    : AvramDividend.Classical.cross_sample_finite_coord_law_of_grid_vector_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:47:22.683874+00:00
-- url     : https://prove2.me/theorems/18a3a4d5-5329-448e-994e-429dff038421
-- title:
--   Cross-space finite coordinate laws inherit a common measurable enumerating grid-vector law
-- statement:
--   For processes on completely different measurable probability spaces, fix any finite set J of times. If a deterministic finite grid contains every time in J and the joint grid-value vector laws agree, then the J-coordinate vector laws also agree. Only time-slice measurability and common grid-vector laws are required. Construct the common coordinate selection map from the enumeration witnesses, show it is measurable, and use functoriality of measure pushforwards. This is the model-independent link between monotone finite-grid laws and the all-finite-coordinate law required by the cross-space path-law identification theorem.
-- source:
--   Pinned Mathlib measurable_pi_iff, measurable_pi_apply, Measure.map_map; supports Proved cross_sample_path_law_eq_of_all_finite_vector_laws [89f430bc-6696-4d3e-a36e-c53345c1341d]. Reuses the mathematical argument of the separately prepared cross_levy_finite_coord_law_of_monotone_enumeration but does not import any Open helper.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.cross_sample_finite_coord_law_of_grid_vector_law
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ℝ≥0 → ℝ)) (Z : Ω₂ → (ℝ≥0 → ℝ))
    (hY : ∀ u : ℝ≥0, Measurable (fun ω => Y ω u))
    (hZ : ∀ u : ℝ≥0, Measurable (fun ω => Z ω u))
    (J : Finset ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ)
    (henum : ∀ j : J, ∃ i : Fin n, t (i.val + 1) = j.1)
    (hGrid :
      Measure.map (fun ω : Ω₁ => fun i : Fin n => Y ω (t (i.val + 1))) P₁ =
      Measure.map (fun ω : Ω₂ => fun i : Fin n => Z ω (t (i.val + 1))) P₂) :
    Measure.map (fun ω : Ω₁ => fun j : J => Y ω j.1) P₁ =
    Measure.map (fun ω : Ω₂ => fun j : J => Z ω j.1) P₂ := by sorry
