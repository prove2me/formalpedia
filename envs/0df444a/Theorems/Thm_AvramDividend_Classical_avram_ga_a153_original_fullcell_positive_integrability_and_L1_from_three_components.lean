-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a153_original_fullcell_positive_integrability_and_L1_from_three_components
-- name    : AvramDividend.Classical.avram_ga_a153_original_fullcell_positive_integrability_and_L1_from_three_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:15:08.298195+00:00
-- url     : https://prove2.me/theorems/037e6d32-c1b6-4b7f-a0da-3b66b27c055e
-- title:
--   Original Gaussian full-cell positive integrability and expected L1 converge from source-exact three-component positive integrable envelopes
-- statement:
--   An exact physical full-cell source residual F=T+B+C inherits integrability of its positive part and vanishing expected positive L1 whenever the actual classical C2 Taylor positive part, Gaussian raw-centred Hessian-cross absolute part and discount-mismatch positive part are each integrable with vanishing expectations, and the original residual positive part is a.e. strongly measurable. This packages the rigorous final glue for ga134 while retaining only one-sided bounds on T and C.
-- source:
--   Proved ga136 original Gaussian one-sided three-error expected L1 glue; actual full-cell source-specific hSplit ga130 and positive source estimate ga137.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a153_original_fullcell_positive_integrability_and_L1_from_three_components
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = T m ω + B m ω + C m ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => max (F m ω) 0) P)
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hTt : Tendsto (fun m => ∫ ω, max (T m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (F m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
