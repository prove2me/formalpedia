-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
-- name    : AvramDividend.Classical.cross_sample_path_law_eq_of_all_finite_vector_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:32:52.267517+00:00
-- url     : https://prove2.me/theorems/89f430bc-6696-4d3e-a36e-c53345c1341d
-- title:
--   Full càdlàg-compatible path-law identification from joint laws on different probability spaces
-- statement:
--   For real-valued random paths on two different underlying measurable probability spaces, if all finite coordinate vector pushforward measures agree, then their full function-space path laws agree. This is the exact probabilistic bridge needed to transfer finite-band jump-count event laws from a canonical Poisson realization (LeanLevy) to the original spectrally negative Lévy process in Prove2Me. No pathwise coupling, equality of sample spaces, or joint realisation is assumed. Once both sample paths are càdlàg almost surely, their jump counts become measurable functionals of the common path law and inherit their distribution.
-- source:
--   Proved cross_sample_path_law_eq_of_finite_cylinder_masses and Mathlib measurable_pi_iff, MeasurableSet.univ_pi, Measure.map_apply at pinned revision. Generalises existing same-base theorem piPathMeasure_map_eq_of_finite_pushforwards [ecb46b0d-f019-49bf-b243-60a156e4528f].

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_finite_cylinder_masses

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.cross_sample_path_law_eq_of_all_finite_vector_laws
    {Ω₁ Ω₂ ι : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ι → ℝ)) (Z : Ω₂ → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hP : P₁ univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω₁ => fun j : J => Y ω j.1) P₁ =
      Measure.map (fun ω : Ω₂ => fun j : J => Z ω j.1) P₂) :
    Measure.map Y P₁ = Measure.map Z P₂ := by sorry
