-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
-- name    : AvramDividend.Classical.avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:29:29.046196+00:00
-- url     : https://prove2.me/theorems/0ab737e5-7a87-4691-8f0c-43e531fffe00
-- title:
--   True Gaussian full-cell positive L1 residual closes from positive Taylor, absolute raw-centred cross and positive discount source errors
-- statement:
--   If the exact original Gaussian physically full compensated spatial residual is F=T+B+C, its positive expected error vanishes provided the positive C2 Taylor remainder, the absolute source raw-centred Hessian cross, and the positive discount mismatch are separately integrable and converge in expected size to zero. The argument uses only max(a+b+c,0) <= max(a,0)+|b|+max(c,0), avoiding the stronger and potentially unavailable full-cell absolute-L1 negative-tail estimate.
-- source:
--   Proved exact original source physical Gaussian full-cell 3-error sum ga130, original compact C2 Taylor ga76, and source cross ga81/ga89.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = T m ω + B m ω + C m ω)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hTt : Tendsto (fun m => ∫ ω, max (T m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
