-- Prove2me | Theorems.Thm_FeynmanKac_augmented_vector_ito_representation
-- name    : FeynmanKac.augmented_vector_ito_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:04:13.77271+00:00
-- url     : https://prove2.me/theorems/578ec085-4ec2-495f-9f3b-1374b2a3e73f
-- title:
--   Clock-augmented Feynman–Kac diffusion admits the upstream vector Itô representation
-- statement:
--   Unpack the canonical IsDiffusion witness for the true two-coordinate diffusion (X,clock). Obtain explicit joint measurability, progressive measurability, and square-integrability of both Brownian coefficient coordinates, together with the complete upstream IsVectorItoVersion representation for the augmented process. This is a genuine stochastic prerequisite, derived from the existing SDE hypothesis, and does not assume the time-dependent Itô formula or martingale conclusion.
-- source:
--   Published IsDiffusion definition KLSModular_FunctionalInequalities_Probability_Diffusion_Setup; FeynmanKac_BoundedDiffusionModel

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion

open MeasureTheory
open scoped NNReal ENNReal

theorem FeynmanKac.augmented_vector_ito_representation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∃ (hm : ∀ (i : Fin 2) (k : Fin 1),
         Measurable (Function.uncurry fun ω s =>
           m.augmentedVolatility (m.augmentedPath s ω) k i))
      (hp : ∀ (i : Fin 2) (k : Fin 1),
         LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration
           (fun ω s => m.augmentedVolatility (m.augmentedPath s ω) k i))
      (hq : ∀ (i : Fin 2) (k : Fin 1) (T : ℝ), 0 < T →
         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
           (‖m.augmentedVolatility (m.augmentedPath s ω) k i‖₊ : ℝ≥0∞)^2
             ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion
        m.brownian m.filtration m.brownianFiltration
        (fun i k ω s => m.augmentedVolatility (m.augmentedPath s ω) k i)
        hm hp hq
        (fun _ => m.initialCoordinates)
        (fun i ω s => m.augmentedDrift (m.augmentedPath s ω) i)
        m.augmentedPath := by sorry
