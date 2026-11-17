-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_nonnegative_L1_convergence_persists_on_restriction
-- name    : AvramDividend.Classical.avram_ga_nonnegative_L1_convergence_persists_on_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:42:27.078704+00:00
-- url     : https://prove2.me/theorems/05cc2f01-d11a-42b7-ad25-17e01a150503
-- title:
--   Nonnegative vanishing integrals remain vanishing on any measure restriction
-- statement:
--   For an arbitrary measure and nonnegative integrable sequence, convergence of the global integrals to zero implies convergence of integrals over every measurable or arbitrary restricted set to zero. Apply monotonicity under measure restriction and the squeeze theorem. This transfers Proved finitecap Hessian cross L1 from P to the positive-clock event P.restrict A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_nonnegative_L1_convergence_persists_on_restriction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (f : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (f m) P)
    (hPos : ∀ m ω, 0 ≤ f m ω)
    (hLim : Tendsto (fun m => ∫ ω, f m ω ∂P) atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, f m ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
