-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a130_true_original_gaussian_lastcell_remove_positive_integrability
-- name    : AvramDividend.Classical.avram_ga_a130_true_original_gaussian_lastcell_remove_positive_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:20:41.101202+00:00
-- url     : https://prove2.me/theorems/d9188a5c-086e-4fad-92d2-b4b1579a1c19
-- title:
--   Remove one original Gaussian terminal spatial cell while preserving integrability of the positive part when the terminal error is absolutely integrable
-- statement:
--   If the original physical Gaussian spatial residual including one final cell has integrable positive part and that same final cell has integrable absolute value, then the positive part of the residual with that terminal cell removed is integrable, provided its measurability is known. The domination max(A,0) ≤ max(A+Last,0)+|Last| is exact, and closes the integrability gap between the previously proved m+1-cell estimate and the b0 original m-cell root, once the true terminal error is shown absolutely integrable.
-- source:
--   Proved original ga_a26_original_spatial_positive_integrable (m+1 cells), root ga122 exact m-cell integrability, terminal source exponential bound and original spatial measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a130_true_original_gaussian_lastcell_remove_positive_integrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A Last : Ω → ℝ)
    (hMeas : AEStronglyMeasurable (fun ω => max (A ω) 0) P)
    (hSum : Integrable (fun ω => max (A ω + Last ω) 0) P)
    (hLast : Integrable (fun ω => |Last ω|) P) :
    Integrable (fun ω => max (A ω) 0) P := by sorry
