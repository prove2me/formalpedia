-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_moving_base_right_generator_of_sublinear_perturbation
-- name    : AvramDividend.Classical.avram_chat07a_original_BV_C1_moving_base_right_generator_of_sublinear_perturbation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:53:37.839512+00:00
-- url     : https://prove2.me/theorems/506652ec-6226-417d-bf09-4e5f047cd452
-- title:
--   Original BV Lévy C¹ generator right slope is stable along o(time) moving reserve bases
-- statement:
--   For an actual original Standing spectrally negative bounded-variation Lévy process, any globally C¹ Lipschitz payoff with the canonical generator integrable at x, and any deterministic moving starting reserve b(h) whose distance to x is o(h) as h decreases to zero from the right, the true transition semigroup increment quotient based at b(h) tends to the same canonical generator value X.generator w x. This is a moving-base right-generator theorem in the genuine X.X(Real.toNNReal h) sample space; it uses the new proved quantitative original semigroup reserve-stability estimate and the proved fixed-base right-generator limit. No fictitious coupling, additional generator assumptions, or stopped Itô assertion is introduced.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), source-faithful BV semigroup localisation. Exact Proved fixed-base global C1 generator UUID b56e7174-ebfe-49ac-899d-0f14fc900201 and Proved two-base normalized semigroup rate UUID 53fabbe9-a624-49db-8095-be1934a174e1. The remaining controlled stopped source jump compensator is not inferred.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07a_original_BV_C1_moving_base_right_generator_of_sublinear_perturbation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (b : ℝ → ℝ)
    (hb : Tendsto (fun h : ℝ => h⁻¹ * |b h - x|)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, w (b h + X.X (Real.toNNReal h) ω) ∂P) - w (b h)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X.generator w x)) := by sorry
