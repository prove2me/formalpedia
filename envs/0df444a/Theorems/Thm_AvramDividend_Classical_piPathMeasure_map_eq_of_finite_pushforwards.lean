-- Prove2me | Theorems.Thm_AvramDividend_Classical_piPathMeasure_map_eq_of_finite_pushforwards
-- name    : AvramDividend.Classical.piPathMeasure_map_eq_of_finite_pushforwards
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:40:39.667559+00:00
-- url     : https://prove2.me/theorems/ecb46b0d-f019-49bf-b243-60a156e4528f
-- title:
--   Full path-law equality from finite-coordinate pushforwards of arbitrary measures
-- statement:
--   For two measurable real-valued random paths driven by potentially different underlying measures, equality of the distributions of all finite-coordinate vectors implies equality of their full function-space pushforward measures, provided the first pushforward has finite mass.
-- source:
--   Generalises the already Proved deterministic-time shifted Lévy path law from finite-dimensional distributions. Crucial for treating the stopped-history restriction P.restrict A and independent original-path law at arbitrary finite stopping times, feeding canonical theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses

open MeasureTheory ProbabilityTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.piPathMeasure_map_eq_of_finite_pushforwards
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {μ ν : Measure Ω}
    (Y Z : Ω → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hMass : (Measure.map Y μ) Set.univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω => fun j : J => Y ω j) μ =
      Measure.map (fun ω : Ω => fun j : J => Z ω j) ν) :
    Measure.map Y μ = Measure.map Z ν := by
  sorry
